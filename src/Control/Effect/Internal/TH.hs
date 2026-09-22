{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Control.Effect.Internal.TH
Description : Template Haskell helpers to generate Alg/Scp effect boilerplate
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides Template Haskell splices that generate common
boilerplate for algebraic effects implemented with the 'Alg' and 'Scp'
wrappers.

There are two families of generators:

  * __Alg-style__ (base functor with continuation @k@):
    'makeAlg', 'makeAlgType', 'makeAlgPattern', 'makeAlgSmart'.

  * __Scp-style__ (scoped effects; payload is a program/value, not a @k@):
    'makeScp', 'makeScpType', 'makeScpPattern', 'makeScpSmart'.

Split variants let you generate only the __type synonym__, only the
__pattern synonym__, or only the __smart constructor(s)__.

=== Examples

@
-- Alg-style base functors
data Put_ s k = Put_ s k
  deriving Functor
newtype Get_ s k = Get_ (s -> k)
  deriving Functor

\$(makeAlg ''Put_)
\$(makeAlg ''Get_)

-- Scp-style base functor
newtype Once_ k = Once_ k
  deriving Functor

\$(makeScp ''Once_)
@
-}
module Control.Effect.Internal.TH (
  makeAlg,
  makeAlgType,
  makeAlgPattern,
  makeAlgSmart,
  makeScp,
  makeScpType,
  makeScpPattern,
  makeScpSmart,
) where

import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Forward
import Control.Effect.Internal.Handler
import Control.Effect.Internal.Prog
import Control.Effect.Internal.Prog.ProgImp (namedCall)
import Control.Monad
import Data.Char
import Data.List
import Language.Haskell.TH

-- This code is best tested by looking at the generated output in GHCi,
-- by using:
--
-- ghci> :set -XTemplateHaskell -XPatternSynonyms -XViewPatterns
-- ghci> :set -XDataKinds -XGADTs -XRankNTypes -XPolyKinds
-- ghci> :set -ddump-splices
-- ghci> :l src/Control/Effect/Internal/TH.hs
--
-- Then, when files that use `$(makeAlg ...)` are used, GHCi will
-- print the spliced code for inspection.

--------------------------------------------------------------------------------
-- Alg generators
--------------------------------------------------------------------------------
data AlgPieces = AlgPieces
  { apTySyn :: Dec
  , apPat :: Dec
  , apPragma :: Dec
  , apSig :: Dec
  , apFun :: Dec
  }

makeAlgPieces :: Name -> Q AlgPieces
makeAlgPieces baseName = do
  info <- reify baseName
  (tvbs, conName, argTys) <- case info of
    TyConI (DataD _ _ tvbs _ [con] _) -> pure (tvbs, conNameOf con, conArgTys con)
    TyConI (NewtypeD _ _ tvbs _ con _) -> pure (tvbs, conNameOf con, conArgTys con)
    _ -> fail "makeAlg: expected data/newtype with a single constructor"

  let tvNames = map tvbName tvbs
  when (null tvNames) $ fail "makeAlg: the base functor must be at least unary (… k)"
  let (paramNames, kName) = (init tvNames, last tvNames)

  freshParams <- mapM (newName . nameBase) paramNames
  let freshK = mkName (nameBase kName)
      substEnv = zip (paramNames ++ [kName]) (map VarT (freshParams ++ [freshK]))

      substT :: [(Name, Type)] -> Type -> Type
      substT env = \case
        VarT n -> case find (\(n0, _) -> nameBase n0 == nameBase n) env of
          Just (_, ty) -> ty
          Nothing -> VarT n
        AppT a b -> AppT (substT env a) (substT env b)
        SigT t k -> SigT (substT env t) k
        ForallT bndrs ctx t ->
          let dropShadow acc tv = filter (\(n0, _) -> nameBase n0 /= nameBase (tvbName tv)) acc
              env' = foldl dropShadow env bndrs
           in ForallT bndrs (map (substT env) ctx) (substT env' t)
        InfixT a n b -> InfixT (substT env a) n (substT env b)
        UInfixT a n b -> UInfixT (substT env a) n (substT env b)
        ParensT t -> ParensT (substT env t)
        t -> t

  when (null argTys) $ fail "makeAlg: constructor must have at least a continuation field"
  let (prefixTys, contTy) = (init argTys, last argTys)

  (retTy, contExpr) <- case stripT contTy of
    VarT v | eqNameBase v kName -> pure (TupleT 0, ConE '())
    t | Just (r, VarT v) <- viewArrow t, eqNameBase v kName -> pure (r, VarE 'id)
    _ -> fail "makeAlg: unsupported continuation shape; expected `k` or `(r -> k)`"

  let retTy' = substT substEnv retTy
      prefixTys' = map (substT substEnv) prefixTys

  let baseStr = nameBase baseName
      effStr = dropTrailingUnderscore baseStr
      effName = mkName effStr
      funName = mkName (lowerHead effStr)

  let effTySyn :: Dec
      effTySyn =
        TySynD
          effName
          (map plainTVCompat freshParams)
          ( AppT
              (ConT ''Alg)
              (applyType (ConT baseName) (map VarT freshParams))
          )

  sigName <- newName "sig"
  let effTy = applyType (ConT effName) (map VarT freshParams)
      memberC = AppT (AppT (ConT ''Member) effTy) (VarT sigName)
      progRes = AppT (AppT (ConT ''Prog) (VarT sigName)) retTy'
      smartTy =
        ForallT
          (map plainTVForall (freshParams ++ [sigName]))
          [memberC]
          (funType prefixTys' progRes)

  xVars <- mapM (\i -> newName ("x" ++ show i)) [1 .. length prefixTys']
  kVar <- newName "k"

  let patArgs = PrefixPatSyn (xVars ++ [kVar])
      scrut = VarE 'prj
      inner = conPCompat 'Just [conPCompat 'Alg [conPCompat conName (map VarP xVars ++ [VarP kVar])]]
      pat = ViewP scrut inner
      builder =
        NormalB
          ( AppE
              (VarE 'inj)
              ( AppE
                  (ConE 'Alg)
                  (applyExp (ConE conName) (map VarE xVars ++ [VarE kVar]))
              )
          )
      patDir = ExplBidir [Clause (map VarP (xVars ++ [kVar])) builder []]
      patDecl = PatSynD (mkName effStr) patArgs patDir pat

  argNames <- mapM (\i -> newName ("a" ++ show i)) [1 .. length prefixTys']
  let smartLhs =
        Clause
          (map VarP argNames)
          ( NormalB
              ( applyExp
                  (VarE 'namedCall)
                  [ LitE (StringL (lowerHead effStr))
                  , ConE 'Alg
                      `AppE` applyExp
                        (ConE conName)
                        (map VarE argNames ++ [contExpr])
                  ]
              )
          )
          --  (ConE 'Alg `AppE`
          --     applyExp (ConE conName)
          --       (map VarE argNames ++ [contExpr]))))
          []
      smartSig = SigD funName smartTy
      smartFun = FunD funName [smartLhs]
      pragma = PragmaD (InlineP funName Inline FunLike AllPhases)

  pure
    AlgPieces
      { apTySyn = effTySyn
      , apPat = patDecl
      , apPragma = pragma
      , apSig = smartSig
      , apFun = smartFun
      }

--------------------------------------------------------------------------------
-- makeAlg: generate Alg-style effect boilerplate from a base functor
--------------------------------------------------------------------------------

{- | Generate the full Alg-style bundle for a base functor @T_@.

Input must be a single-constructor @data@/@newtype@ whose /last field/
is the continuation @k@ (either @k@ or @(r -> k)@).

Produces:

  * @type T params = Alg (T_ params)@
  * a bidirectional @pattern T ...@ matching/injecting @inj (Alg (Con ...))@
  * a smart constructor (lower-cased name):
      - if the continuation is @k@, returns @Prog sig ()@ and passes @()@
      - if the continuation is @(r -> k)@, returns @Prog sig r@ and uses @id@

Example:
@
data Put_ s k = Put_ s k
  deriving Functor
makeAlg (''Put_ s)
@
This will generate:
@
type Put s = Alg (Put_ s)

pattern Put :: Member (Put s) effs => s -> k -> Effs effs m k
pattern Put s k <- (prj -> Just (Alg (Put_ s k)))
  where Put s k = inj (Alg (Put_ s k))

{\-# INLINE put #-\}
put :: Member (Put s) sig => s -> Prog sig ()
put s = call (Alg (Put_ s ()))
@
-}
makeAlg :: Name -> Q [Dec]
makeAlg baseName = do
  AlgPieces{..} <- makeAlgPieces baseName
  pure [apTySyn, apPat, apPragma, apSig, apFun]

-- | Generate only the Alg-style /type synonym/.
makeAlgType :: Name -> Q [Dec]
makeAlgType baseName = do
  AlgPieces{..} <- makeAlgPieces baseName
  pure [apTySyn]

-- | Generate only the Alg-style /pattern synonym/ (bidirectional).
makeAlgPattern :: Name -> Q [Dec]
makeAlgPattern baseName = do
  AlgPieces{..} <- makeAlgPieces baseName
  pure [apPat]

-- | Generate only the Alg-style smart constructor (with @INLINE@ and explicit type).
makeAlgSmart :: Name -> Q [Dec]
makeAlgSmart baseName = do
  AlgPieces{..} <- makeAlgPieces baseName
  pure [apPragma, apSig, apFun]

--------------------------------------------------------------------------------
-- Scp generators
--------------------------------------------------------------------------------

data ScpPieces = ScpPieces
  { spTySyn :: Dec
  , spPat :: Dec
  , spPragma :: Dec
  , spSig :: Dec
  , spFun :: Dec
  , spMPragma :: Dec
  , spMSig :: Dec
  , spMFun :: Dec
  }

makeScpPieces :: Name -> Q ScpPieces
makeScpPieces baseName = do
  info <- reify baseName
  (tvbs, conName, _argTys) <- case info of
    TyConI (DataD _ _ tvbs _ [con] _) -> pure (tvbs, conNameOf con, conArgTys con)
    TyConI (NewtypeD _ _ tvbs _ con _) -> pure (tvbs, conNameOf con, conArgTys con)
    _ -> fail "makeScp: expected data/newtype with a single constructor"

  let tvNames = map tvbName tvbs
  when (null tvNames) $ fail "makeScp: the base functor must be at least unary (… k)"
  let paramNames = init tvNames -- drop the final program/result parameter `k`
  freshParams <- mapM (newName . nameBase) paramNames

  let baseStr = nameBase baseName
      effStr = dropTrailingUnderscore baseStr
      effName = mkName effStr
      funName = mkName (lowerHead effStr)

  -- type Eff params = Scp Base params
  let effTySyn :: Dec
      effTySyn =
        TySynD
          effName
          (map plainTVCompat freshParams)
          ( AppT
              (ConT ''Scp)
              (applyType (ConT baseName) (map VarT freshParams))
          )

  -- Build: forall params a sig. Member (Eff params) sig => Prog sig a -> Prog sig a
  sigName <- newName "sig"
  aName <- newName "a"

  let effTy = applyType (ConT effName) (map VarT freshParams)
      memberC = AppT (AppT (ConT ''Member) effTy) (VarT sigName)
      argTy = AppT (AppT (ConT ''Prog) (VarT sigName)) (VarT aName)
      resTy = argTy
      smartTy =
        ForallT
          (map plainTVForall (freshParams ++ [aName, sigName]))
          [memberC]
          (AppT (AppT ArrowT argTy) resTy)

  -- Pattern: pattern Eff p <- (prj -> Just (Scp (Con p))) where Eff p = inj (Scp (Con p))
  pVar <- newName "p"
  let patArgs = PrefixPatSyn [pVar]
      scrut = VarE 'prj
      inner = conPCompat 'Just [conPCompat 'Scp [conPCompat conName [VarP pVar]]]
      pat = ViewP scrut inner
      builder =
        NormalB
          ( AppE
              (VarE 'inj)
              ( AppE
                  (ConE 'Scp)
                  (applyExp (ConE conName) [VarE pVar])
              )
          )
      patDir = ExplBidir [Clause [VarP pVar] builder []]
      patDecl = PatSynD (mkName effStr) patArgs patDir pat

  -- Smart constructor: effName p = call (Scp (Con p))
  pArg <- newName "p"
  let smartLhs =
        Clause
          [VarP pArg]
          ( NormalB
              ( VarE 'call
                  `AppE` ( ConE 'Scp
                             `AppE` applyExp (ConE conName) [VarE pArg]
                         )
              )
          )
          []
      smartSig = SigD funName smartTy
      smartFun = FunD funName [smartLhs]
      pragma = PragmaD (InlineP funName Inline FunLike AllPhases)

  -- Monadic handler smart constructor: effNameM
  let funNameM = mkName (lowerHead effStr ++ "M")
  mName <- newName "m"
  xName <- newName "x" -- inner forall
  aName <- newName "a" -- outer result
  let monadC = AppT (ConT ''Monad) (VarT mName)
      effsTy = AppT (AppT (AppT (ConT ''Effs) (VarT sigName)) (VarT mName)) (VarT xName)
      algArgTy =
        ForallT
          [plainTVForall xName]
          []
          ( AppT
              (AppT ArrowT effsTy)
              (AppT (VarT mName) (VarT xName))
          )
      argTyOuter = AppT (VarT mName) (VarT aName)
      resTyOuter = argTyOuter
      smartMTy =
        ForallT
          (map plainTVForall (freshParams ++ [aName, mName, sigName]))
          [memberC, monadC]
          (funType [algArgTy, argTyOuter] resTyOuter)

  algVar <- newName "alg"
  pArgM <- newName "p"
  let dotAlgInj = AppE (AppE (VarE '(.)) (VarE algVar)) (VarE 'inj)
      scopeExp = AppE (ConE 'Scp) (applyExp (ConE conName) [VarE pArgM])
      bodyM = NormalB (AppE dotAlgInj scopeExp)
      smartMSig = SigD funNameM smartMTy
      smartMFun = FunD funNameM [Clause [VarP algVar, VarP pArgM] bodyM []]
      pragmaM = PragmaD (InlineP funNameM Inline FunLike AllPhases)

  pure
    ScpPieces
      { spTySyn = effTySyn
      , spPat = patDecl
      , spPragma = pragma
      , spSig = smartSig
      , spFun = smartFun
      , spMPragma = pragmaM
      , spMSig = smartMSig
      , spMFun = smartMFun
      }

--------------------------------------------------------------------------------
-- makeScp: generate Scp-style effect boilerplate from a base functor
--------------------------------------------------------------------------------

{- | Generate the full Scp-style bundle for a scoped base functor @T_@.

Input must be a single-constructor @data@/@newtype@ whose (typically only)
field is the /payload program or value/ (no @k@).

Produces:

  * @type T params = Scp (T_ params)@
  * a bidirectional @pattern T p@ under 'Scp'
  * two smart constructors:
      - @t  :: Member T sig => Prog sig a -> Prog sig a@
      - @tM :: (Monad m, Member T sig)
            => (forall x. Effs sig m x -> m x) -> m a -> m a@
-}
makeScp :: Name -> Q [Dec]
makeScp baseName = do
  ScpPieces{..} <- makeScpPieces baseName
  pure [spTySyn, spPat, spPragma, spSig, spFun, spMPragma, spMSig, spMFun]

-- | Generate only the Scp-style /type synonym/.
makeScpType :: Name -> Q [Dec]
makeScpType baseName = do
  ScpPieces{..} <- makeScpPieces baseName
  pure [spTySyn]

-- | Generate only the Scp-style /pattern synonym/ (bidirectional).
makeScpPattern :: Name -> Q [Dec]
makeScpPattern baseName = do
  ScpPieces{..} <- makeScpPieces baseName
  pure [spPat]

{- | Generate only the Scp-style smart constructors (plain + monadic),
each with @INLINE@ and explicit types.
-}
makeScpSmart :: Name -> Q [Dec]
makeScpSmart baseName = do
  ScpPieces{..} <- makeScpPieces baseName
  pure [spPragma, spSig, spFun, spMPragma, spMSig, spMFun]

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- Extract the constructor name
conNameOf :: Con -> Name
conNameOf = \case
  NormalC n _ -> n
  RecC n _ -> n
  InfixC _ n _ -> n
  ForallC _ _ c -> conNameOf c
  GadtC [n] _ _ -> n
  RecGadtC [n] _ _ -> n
  _ -> error "makeAlg: unsupported constructor form"

-- Extract the argument types of a constructor
conArgTys :: Con -> [Type]
conArgTys = \case
  NormalC _ bs -> map snd bs
  RecC _ bs -> [t | (_, _, t) <- bs]
  InfixC a _ b -> [snd a, snd b]
  ForallC _ _ c -> conArgTys c
  GadtC _ bs _ -> map snd bs
  RecGadtC _ bs _ -> [t | (_, _, t) <- bs]

-- Apply a type to many type arguments
applyType :: Type -> [Type] -> Type
applyType = foldl AppT

-- Apply an expression to many expression arguments
applyExp :: Exp -> [Exp] -> Exp
applyExp = foldl AppE

-- Lowercase the first character of a name
lowerHead :: String -> String
lowerHead [] = []
lowerHead (c : cs) = toLower c : cs

-- TyVarBndr name extraction across TH versions
#if MIN_VERSION_template_haskell(2,17,0)
tvbName :: TyVarBndr flag -> Name
tvbName (PlainTV n _)    = n
tvbName (KindedTV n _ _) = n
#else
tvbName :: TyVarBndr -> Name
tvbName (PlainTV n)      = n
tvbName (KindedTV n _)   = n
#endif

eqNameBase :: Name -> Name -> Bool
eqNameBase a b = nameBase a == nameBase b

stripT :: Type -> Type
stripT = \case
  ParensT t -> stripT t
  SigT t _ -> stripT t
  ForallT _ _ t -> stripT t
  t -> t

viewArrow :: Type -> Maybe (Type, Type)
viewArrow t = case stripT t of
  AppT (AppT ArrowT a) b -> Just (a, b)
  InfixT a n b | n == ''(->) -> Just (a, b)
  UInfixT a n b | n == ''(->) -> Just (a, b)
  _ -> Nothing

funType :: [Type] -> Type -> Type
funType args res = foldr (\a b -> AppT (AppT ArrowT a) b) res args

-- Drop trailing underscore in a base functor name (e.g. Put_ -> Put)
dropTrailingUnderscore :: String -> String
dropTrailingUnderscore sxx = case reverse sxx of
  ('_' : xs) -> reverse xs
  _ -> sxx

#if MIN_VERSION_template_haskell(2,21,0)
plainTVCompat :: Name -> TyVarBndr BndrVis
plainTVCompat n = PlainTV n BndrReq

plainTVForall :: Name -> TyVarBndr Specificity
plainTVForall n = PlainTV n SpecifiedSpec
#elif MIN_VERSION_template_haskell(2,18,0)
plainTVCompat :: Name -> TyVarBndr ()
plainTVCompat n = PlainTV n ()

plainTVForall :: Name -> TyVarBndr Specificity
plainTVForall n = PlainTV n SpecifiedSpec
#elif MIN_VERSION_template_haskell(2,17,0)
plainTVCompat :: Name -> TyVarBndr Specificity
plainTVCompat n = PlainTV n SpecifiedSpec

plainTVForall :: Name -> TyVarBndr Specificity
plainTVForall n = PlainTV n SpecifiedSpec
#else
plainTVCompat :: Name -> TyVarBndr
plainTVCompat n = PlainTV n

plainTVForall :: Name -> TyVarBndr
plainTVForall n = PlainTV n
#endif

#if MIN_VERSION_template_haskell(2,18,0)
conPCompat :: Name -> [Pat] -> Pat
conPCompat n ps = ConP n [] ps
#else
conPCompat :: Name -> [Pat] -> Pat
conPCompat n ps = ConP n ps
#endif
