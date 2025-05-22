{-|
Module      : Control.Effect.Internal.AlgTrans
Description : Transforming effectful operations along carrier transformers
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental

This module contains combinators of /algebra transformers/, the core data type
of this library. 
-}
{-# LANGUAGE ImpredicativeTypes, QuantifiedConstraints, UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds, LambdaCase, BlockArguments #-}
{-# LANGUAGE PartialTypeSignatures, MagicHash, PartialTypeSignatures #-}

module Control.Effect.Internal.AlgTrans where

import Data.List.Kind 
import Data.HFunctor ( HFunctor )
import Data.Proxy

import Control.Effect.Internal.Effs
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Prog.ProgImp ( Prog, eval )
import Control.Effect.Internal.Forward

-- * Using algebra transformers and runners 

-- | Evaluating a program with an algebra transformer.
{-# INLINE evalTr #-}
evalTr :: forall effs oeffs xeffs ts cs m a.
       ( HFunctor (Effs effs)
       , cs m
       , Injects oeffs xeffs
       , Monad (Apply ts m) )
       => Algebra xeffs m
       -> AlgTrans effs oeffs ts cs
       -> Prog effs a
       -> Apply ts m a
evalTr oalg alg = eval (getAT alg (oalg . injs)) 

-- | Evaluating a program with an algebra transformer that outputs no effects.
{-# INLINE evalTr' #-}
evalTr' :: forall m effs ts cs a. 
        ( HFunctor (Effs effs) 
        , cs m
        , Monad (Apply ts m) )
        => AlgTrans effs '[] ts cs
        -> Prog effs a
        -> Apply ts m a
evalTr' alg = eval (getAT alg (absurdEffs @m)) 

-- * Building algebra transformers

-- ** Primitive combinators

-- | Treating an algebra on @m@ as a trivial algebra transformer that only works
-- when the carrier is exactly @m@.
{-# INLINE asAT #-}
asAT :: forall effs m. Algebra effs m -> AlgTrans effs '[] '[] ((~) m)
asAT alg = AlgTrans \_ -> alg

-- | The identity algebra transformer.
{-# INLINE idAT #-}
idAT :: forall effs cs. AlgTrans effs effs '[] cs
idAT = AlgTrans \alg -> alg

-- In this library, constraints with names ending with a hash will always be 
-- satisfied matically when the parameters are substituted by concrete values. 
-- Users don't need to care about them.

type CompAT# ts1 ts2 effs1 cs2 = ( forall m . Assoc ts1 ts2 m )

-- | Composing two algebra transformers.
{-# INLINE compAT #-}
compAT :: forall effs1 effs2 effs3 ts1 ts2 cs1 cs2.
          ( CompAT# ts1 ts2 effs1 cs2 )
       => AlgTrans effs1 effs2 ts1 cs1
       -> AlgTrans effs2 effs3 ts2 cs2
       -> AlgTrans effs1 effs3 (ts1 :++ ts2) (CompC ts2 cs1 cs2)
compAT alg1 alg2 = AlgTrans \(oalg :: Algebra effs3 m) -> getAT alg1 (getAT alg2 oalg) 

-- | Every algebra transformer can be used as one that processes fewer input effects,
-- generating more output effects, and/or with stronger carrier constraints.
{-# INLINE weakenAT #-}
weakenAT :: forall effs' oeffs' cs' effs oeffs cs ts.
            (Injects effs' effs, Injects oeffs oeffs', forall m. cs' m => cs m)
         => AlgTrans effs  oeffs  ts cs
         -> AlgTrans effs' oeffs' ts cs'
weakenAT at = AlgTrans \oalg x -> getAT at (oalg . injs) (injs x)

type CaseTrans# effs1 effs2 = 
  ( Append effs1 (effs2 :\\ effs1)
  , Injects (effs2 :\\ effs1) effs2 )

-- | Case splitting on the union of two effect rows. Note that `Union` is defined
-- two be @effs1 ++ (effs2 :\\ effs1)@, so if an effect @e@ is both a member of @effs1@ 
-- and @effs2@, it is consumed by the first algebra transformer.
{-# INLINE caseAT #-}
caseAT :: forall effs1 effs2 cs1 cs2 oeffs ts. 
          CaseTrans# effs1 effs2
       => AlgTrans effs1 oeffs ts cs1
       -> AlgTrans effs2 oeffs ts cs2
       -> AlgTrans (effs1 `Union` effs2) oeffs ts (AndC cs1 cs2)
caseAT at1 at2 = AlgTrans \oalg -> hunion (getAT at1 oalg) (getAT at2 oalg)

type CaseTrans'# effs1 effs2 = (Append effs1 effs2)

-- | Case splitting on the concatenation of two effect rows.
{-# INLINE caseAT' #-}
caseAT' :: forall effs1 effs2 cs1 cs2 oeffs ts. 
          (CaseTrans'# effs1 effs2)
        => AlgTrans effs1 oeffs ts cs1
        -> AlgTrans effs2 oeffs ts cs2
        -> AlgTrans (effs1 :++ effs2) oeffs ts (AndC cs1 cs2)
caseAT' at1 at2 = AlgTrans \oalg -> heither (getAT at1 oalg) (getAT at2 oalg)


-- ** Derived combinators of algebra transformers

-- | Algebra transformer for a single effect.
{-# INLINE algTrans1 #-}
algTrans1 :: (forall m. cs m => Algebra oeffs m 
                -> forall x. eff (Apply ts m) x -> Apply ts m x)
          -> AlgTrans '[eff] oeffs ts cs
algTrans1 at = AlgTrans \oalg (o :: Effs '[eff] _ _) -> 
   case prj @eff o of Just o' -> at oalg o'

-- | Replace the carrier constraint of an algebra transformer with a strong one.
{-# INLINE weakenC #-}
weakenC :: forall cs' cs effs oeffs ts. 
          (forall m. cs' m => cs m)
       => AlgTrans effs oeffs ts cs
       -> AlgTrans effs oeffs ts cs'
weakenC at = AlgTrans \oalg x -> getAT at oalg x

-- | Replace the carrier constraint @cs@ of an algebra transformer with the conjunction
-- of @cs@ and another constraint @cs'@.
{-# INLINE weakenCAnd #-}
weakenCAnd :: forall cs' cs effs oeffs ts. 
          AlgTrans effs oeffs ts cs
       -> AlgTrans effs oeffs ts (AndC cs cs')
weakenCAnd at = AlgTrans \oalg x -> getAT at oalg x

-- | Forget some input effects and add some unused output effects.
{-# INLINE weakenEffs #-}
weakenEffs 
       :: (Injects effs' effs, Injects oeffs oeffs')
       => AlgTrans effs  oeffs  ts cs
       -> AlgTrans effs' oeffs' ts cs
weakenEffs = weakenAT

-- | Add some unused output effects.
{-# INLINE weakenOEffs #-}
weakenOEffs :: forall oeffs' oeffs effs ts cs. 
          Injects oeffs oeffs'
       => AlgTrans effs oeffs  ts cs
       -> AlgTrans effs oeffs' ts cs
weakenOEffs at = AlgTrans \ oalg x -> getAT at (oalg . injs) x

-- | Forget some input effects of an algebra transformer.
{-# INLINE weakenIEffs #-}
weakenIEffs :: forall effs' effs oeffs ts cs.
          Injects effs' effs
       => AlgTrans effs  oeffs ts cs
       -> AlgTrans effs' oeffs ts cs
weakenIEffs at = AlgTrans \ oalg x -> getAT at oalg (injs x)

type HideAT# effs effs' = (Injects (effs :\\ effs') effs)

-- | Forget some input effects @effs'@.
{-# INLINE hideAT #-}
hideAT :: forall effs' effs oeffs ts cs.
          HideAT# effs effs'
       => AlgTrans effs  oeffs ts cs
       -> AlgTrans (effs :\\ effs') oeffs ts cs
hideAT at = AlgTrans \ oalg x -> getAT at oalg (injs x)

-- | Case splitting with the same carrier constraint.
{-# INLINE caseATSameC #-}
caseATSameC 
       :: forall effs1 effs2 cs oeffs ts. 
          CaseTrans# effs1 effs2
       => AlgTrans effs1 oeffs ts cs
       -> AlgTrans effs2 oeffs ts cs
       -> AlgTrans (effs1 `Union` effs2) oeffs ts cs
caseATSameC at1 at2 = weakenC (caseAT at1 at2)

-- | Case splitting with the same carrier constraint.
{-# INLINE caseATSameC' #-}
caseATSameC'
       :: forall effs1 effs2 cs oeffs ts. 
           CaseTrans'# effs1 effs2
        => AlgTrans effs1 oeffs ts cs
        -> AlgTrans effs2 oeffs ts cs
        -> AlgTrans (effs1 :++ effs2) oeffs ts cs
caseATSameC' at1 at2 = weakenC (caseAT' at1 at2)

type UnionAT# effs1 effs2 oeffs1 oeffs2 = 
  ( Injects effs1 effs1, Injects effs2 effs2
  , Injects oeffs1 (oeffs1 `Union` oeffs2)
  , Injects oeffs2 (oeffs1 `Union` oeffs2)
  , CaseTrans# effs1 effs2)

-- | The most general form of case splitting on the union of input effects.
unionAT :: forall effs1 effs2 oeffs1 oeffs2 cs1 cs2 ts. 
           UnionAT# effs1 effs2 oeffs1 oeffs2
        => AlgTrans effs1 oeffs1 ts cs1
        -> AlgTrans effs2 oeffs2 ts cs2
        -> AlgTrans (effs1 `Union` effs2) (oeffs1 `Union` oeffs2) ts (AndC cs1 cs2)
unionAT at1 at2 = caseAT (weakenAT @effs1 at1) (weakenAT @effs2 at2)

type AppendAT# effs1 effs2 oeffs1 oeffs2 = 
  ( Injects effs1 effs1, Injects effs2 effs2
  , Injects oeffs1 (oeffs1 :++ oeffs2)
  , Injects oeffs2 (oeffs1 :++ oeffs2)
  , CaseTrans'# effs1 effs2)

-- | The most general form of case splitting on the concatenation of input effects.
appendAT :: forall effs1 effs2 oeffs1 oeffs2 cs1 cs2 ts. 
            AppendAT# effs1 effs2 oeffs1 oeffs2
         => AlgTrans effs1 oeffs1 ts cs1
         -> AlgTrans effs2 oeffs2 ts cs2
         -> AlgTrans (effs1 :++ effs2) (oeffs1 :++ oeffs2) ts (AndC cs1 cs2)
appendAT at1 at2 = caseAT' (weakenAT @effs1 at1) (weakenAT @effs2 at2)

type WithFwds# effs oeffs xeffs = 
  ( CaseTrans# effs xeffs
  , Injects xeffs xeffs
  , Injects effs effs
  , Injects oeffs (oeffs `Union` xeffs)
  , Injects xeffs (oeffs `Union` xeffs) )

-- | Bypassing some forwardable effects @xeffs@ along an algebra transformer. 
-- Members of @xeffs@ that are already in @effs@ or @xeffs@ are ignored. 
{-# INLINE withFwds #-}
withFwds :: forall xeffs effs oeffs ts cs. 
            ( ForwardsC cs xeffs ts
            , WithFwds# effs oeffs xeffs )
         => Proxy xeffs
         -> AlgTrans effs oeffs ts cs
         -> AlgTrans (effs `Union` xeffs) (oeffs `Union` xeffs) ts cs
withFwds _ at = weakenC (unionAT at (fwds @xeffs))

type WithFwds'# effs oeffs xeffs = 
  ( Append effs xeffs
  , Injects xeffs xeffs
  , Injects effs effs
  , Injects oeffs (oeffs :++ xeffs)
  , Injects xeffs (oeffs :++ xeffs) )

-- | Bypassing a forwardable effect along an algebra transformer.
{-# INLINE withFwds' #-}
withFwds' :: forall xeffs effs oeffs ts cs. 
            ( ForwardsC cs xeffs ts
            , WithFwds'# effs oeffs xeffs )
         => Proxy xeffs
         -> AlgTrans effs oeffs ts cs
         -> AlgTrans (effs :++ xeffs) (oeffs :++ xeffs)ts cs
withFwds' _ at = weakenC (appendAT at (fwds @xeffs))

-- ** Fusion-based combinators
type FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 = 
   ( GeneralFuseAT# effs2 effs2 effs1 effs2 oeffs1 oeffs2 ts1 ts2
   , Injects effs2 effs2 )

infixr 9 `fuseAT`, `fuseAT'`

-- | @fuseAT at1 at2@ composes @at1@ and @at2@ in a way that uses @at2@ maximally:
--    1. all the input effects @effs2@ of @at2@ are visible in the input effects of the final result, and
--    2. the output effects @oeffs1@ of @at1@ are intercepted by @effs2@ as much as possible.
{-# INLINE fuseAT #-}
fuseAT :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
          FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 
       => (ForwardsC cs1 effs2 ts1, ForwardsC cs2 (oeffs1 :\\ effs2) ts2)
       => AlgTrans effs1 oeffs1 ts1 cs1 
       -> AlgTrans effs2 oeffs2 ts2 cs2
       -> AlgTrans (effs1 `Union` effs2) 
                   ((oeffs1 :\\ effs2) `Union` oeffs2) 
                   (ts1 :++ ts2)
                   (CompC ts2 cs1 cs2)
fuseAT at1 at2 = generalFuseAT (Proxy @effs2) (Proxy @effs2) at1 at2

-- | A variant of `fuseAT` that demands the carrier constraint @cs1@ of the 
-- first algebra transformer is always satisfied by @Apply ts2 m@ whenever @cs2 m@
-- holds. This is useful for keeping the constraints simple.
{-# INLINE fuseAT' #-}
fuseAT' :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
          FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 
       => (ForwardsC cs1 effs2 ts1, ForwardsC cs2 (oeffs1 :\\ effs2) ts2,
           forall m. cs2 m => cs1 (Apply ts2 m))
       => AlgTrans effs1 oeffs1 ts1 cs1 
       -> AlgTrans effs2 oeffs2 ts2 cs2
       -> AlgTrans (effs1 `Union` effs2) 
                   ((oeffs1 :\\ effs2) `Union` oeffs2) 
                   (ts1 :++ ts2)
                   cs2
fuseAT' at1 at2 = weakenC (fuseAT at1 at2)


infixr 9 `pipeAT`

type PipeAT# effs2 oeffs1 oeffs2 ts1 ts2 = 
   ( Injects (oeffs1 :\\ effs2) ((oeffs1 :\\ effs2) `Union` oeffs2)
   , Injects oeffs2 ((oeffs1 :\\ effs2) `Union` oeffs2)
   , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
   , Append (oeffs1 :\\ effs2) effs2
   , forall m . Assoc ts1 ts2 m )

-- | @pipeAT at1 at2@ composes @at1@ and @at2@ in a way that 
--    1. the input effects @effs2@ of @at2@ are /not/ visible in the input effects of the final result, and
--    2. the output effects @oeffs1@ of @at1@ are intercepted by @effs2@ as much as possible.
{-# INLINE pipeAT #-}
pipeAT :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
          ( ForwardsC cs2 (oeffs1 :\\ effs2) ts2
          , PipeAT# effs2 oeffs1 oeffs2 ts1 ts2 )
       => AlgTrans effs1 oeffs1 ts1 cs1 
       -> AlgTrans effs2 oeffs2 ts2 cs2
       -> AlgTrans effs1 
                   ((oeffs1 :\\ effs2) `Union` oeffs2) 
                   (ts1 :++ ts2)
                   (CompC ts2 cs1 cs2)

-- We can define pipeAT as:
--
-- > pipeAT at1 at2 = generalFuse (Proxy @'[]) (Proxy @effs2) at1 at2
-- 
-- But this would result in some always true but complex constraints, so let's
-- give a direct definition:

pipeAT at1 at2 = AlgTrans $ \oalg -> 
  getAT at1 (weakenAlg $
    heither @(oeffs1 :\\ effs2) @effs2
      (getAT (fwds @(oeffs1 :\\ effs2) @ts2) (weakenAlg oalg))
      (getAT at2 (weakenAlg oalg)))


infixr 9 `passAT`

type PassAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 = 
   ( Injects (effs2 :\\ effs1) effs2
   , Injects oeffs2 (oeffs1 `Union` oeffs2)
   , Injects oeffs1 (oeffs1 `Union` oeffs2)
   , Append effs1 (effs2 :\\ effs1)
   , forall m. Assoc ts1 ts2 m )

-- | @passAT at1 at2@ composes @at1@ and @at2@ in a way that 
--    1. all the input effects @effs2@ of @at2@ are visible in the input effects of the final result, and
--    2. the output effects @oeffs1@ of @at1@ are /not/ intercepted by @effs2@ at all.
-- If an effect is in the intersection of @effs1@ and @effs2@, it is handled by @at1@.
{-# INLINE passAT #-}
passAT :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
          ( ForwardsC cs1 effs2 ts1
          , ForwardsC cs2 oeffs1 ts2
          , PassAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 )
       => AlgTrans effs1 oeffs1 ts1 cs1 
       -> AlgTrans effs2 oeffs2 ts2 cs2
       -> AlgTrans (effs1 `Union` effs2) 
                   (oeffs1 `Union` oeffs2) 
                   (ts1 :++ ts2)
                   (CompC ts2 cs1 cs2)
passAT at1 at2 = AlgTrans $ \(oalg :: Algebra _ m) -> 
  hunion @effs1 @effs2
    (getAT at1 @(Apply ts2 m) (getAT (fwds @oeffs1 @ts2) @m (oalg . injs)))
    (getAT (fwds @effs2 @ts1) (getAT at2 (oalg . injs)))


type PassAT'# effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 = 
   (  Injects (effs1 :\\ effs2) effs1
    , Injects oeffs2 (oeffs1 `Union` oeffs2)
    , Injects oeffs1 (oeffs1 `Union` oeffs2)
    , Injects (effs1 `Union` effs2) (effs2 `Union` effs1)
    , Append effs2 (effs1 :\\ effs2)
    , forall m . Assoc ts1 ts2 m )

infixr 9 `passAT'`

-- | @passAT' at1 at2@ is the same as `passAT` except that if an effect is in the 
-- intersection of @effs1@ and @effs2@, it is handled by @at2@.
{-# INLINE passAT' #-}
passAT' :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
        ( ForwardsC cs1 effs2 ts1
        , ForwardsC cs2 oeffs1 ts2
        , PassAT'# effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 )
        => AlgTrans effs1 oeffs1 ts1 cs1 
        -> AlgTrans effs2 oeffs2 ts2 cs2
        -> AlgTrans (effs1 `Union` effs2) 
                    (oeffs1 `Union` oeffs2) 
                    (ts1 :++ ts2)
                    (CompC ts2 cs1 cs2)
passAT' at1 at2 = AlgTrans $ \(oalg :: Algebra _ m) -> 
  hunion @effs2 @effs1
      (getAT (fwds @effs2 @ts1) (getAT at2 (oalg . injs)))
      (getAT at1 (getAT (fwds @oeffs1 @ts2) (oalg . injs)))
  . injs

type GeneralFuseAT# feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 =
   ( Append effs1 (feffs :\\ effs1)
   , Injects (feffs :\\ effs1) feffs
   , forall m . Assoc ts1 ts2 m
   , Append (oeffs1 :\\ ieffs) ieffs
   , Injects oeffs1 ((oeffs1 :\\ ieffs) :++ ieffs)
   , Injects oeffs2             ((oeffs1 :\\ ieffs) :++ (oeffs2 :\\ (oeffs1 :\\ ieffs))) 
   , Injects (oeffs1 :\\ ieffs) ((oeffs1 :\\ ieffs) :++ (oeffs2 :\\ (oeffs1 :\\ ieffs)))
   )

{-# INLINE generalFuseAT #-}
-- | `generalFuseAT` subsumes @fuseAT@, @passAT@, and @pipeAT@ by having two type arguments
-- @feffs@ and @ieffs@ such that
--   1. @feffs@ is a subset of @effs2@ and it specifies the effects that we want to be
--      forwarded along @ts1@ and exposed by the resulting handler;
--   2. @ieffs@ is a subset of @effs2@ and it specifies the effects that we want to 
--      use to intercept the effects produced by @h1@. 
-- Therefore @generalFuseAT@ instantiates to
--   1. `fuseAT` with @feffs ~ effs2@ and @ieffs ~ effs2@,
--   2. `pipeAT` with @feffs ~ []@    and @ieffs ~ effs2@,
--   3. `passAT` with @feffs ~ effs2@ and @ieffs ~ []@.
-- (When both @feffs@ and @ieffs@ are empty, @generalFuse@ becomes useless so there
-- isn't this case defined specially.)
generalFuseAT
  :: forall feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( Injects feffs effs2
     , Injects ieffs effs2
     , ForwardsC cs1 feffs ts1
     , ForwardsC cs2 (oeffs1 :\\ ieffs) ts2
     , GeneralFuseAT# feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 )
  => Proxy feffs 
  -> Proxy ieffs 
  -> AlgTrans effs1 oeffs1 ts1 cs1 
  -> AlgTrans effs2 oeffs2 ts2 cs2
  -> AlgTrans (effs1 `Union` feffs) 
              ((oeffs1 :\\ ieffs) `Union` oeffs2)
              (ts1 :++ ts2)
              (CompC ts2 cs1 cs2)
generalFuseAT _ _ at1 at2 = AlgTrans $ \oalg ->
   hunion @effs1 @feffs
     (getAT at1 (weakenAlg $
       heither @(oeffs1 :\\ ieffs) @ieffs
         (getAT (fwds @(oeffs1 :\\ ieffs) @ts2) (weakenAlg oalg))
         (weakenAlg (getAT at2 (weakenAlg oalg)))))
     (getAT (fwds @feffs @ts1) (weakenAlg (getAT at2 (weakenAlg oalg))))