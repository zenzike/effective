{-|
Module      : Control.Effect.Plugin
Description : Type-checking plugin 
License     : BSD-3-Clause
Author      : Zhixuan Yang
Stability   : experimental

The code in this file was adapted from Andrzej Rybczak's plugin for the
@effectful@ library, released under the license below. Andrzej's code
in turn was based on Xy Ren's code of the plugin for the @cleff@ library. 

--------------------------------------------------------------------------------
Copyright (c) 2021-2022, Andrzej Rybczak

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

    * Neither the name of Andrzej Rybczak nor the names of other
      contributors may be used to endorse or promote products derived
      from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

This software incorporates code from the cleff package (available from
https://hackage.haskell.org/package/cleff) under the following license:

Copyright Xy Ren (c) 2022

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

    * Neither the name of Xy Ren nor the names of other contributors
      may be used to endorse or promote products derived from this
      software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
--------------------------------------------------------------------------------
-}
{-# LANGUAGE CPP, LambdaCase, NoFieldSelectors, OverloadedRecordDot, DuplicateRecordFields, RecordWildCards #-}
module Control.Effect.Plugin (plugin) where

import Data.Bifunctor
import Data.Coerce
import Data.Either
import Data.Foldable
import Control.Monad 
import Data.IORef
import Data.Maybe
import Data.Set qualified as S
import GHC.Core.Class
import GHC.Core.InstEnv
import GHC.Core.Predicate
import GHC.Core.TyCo.Rep
import GHC.Core.TyCo.Subst
import GHC.Core.TyCon
import GHC.Core.Type
import GHC.Core.Unify
import GHC.Driver.Env
import GHC.Driver.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.TcType
import GHC.Types.Name
import GHC.Types.Unique.FM
import GHC.Types.Unique.Set
import GHC.Types.Var.Set
import GHC.Unit.Finder
import GHC.Unit.Module
import GHC.Utils.Outputable qualified as O
import GHC.Clock
import Data.List.NonEmpty (NonEmpty(..))

#if __GLASGOW_HASKELL__ <= 912 && __GLASGOW_HASKELL__ > 902
import GHC.Driver.Config.Finder
#endif

#if __GLASGOW_HASKELL__ >= 912
import GHC.Tc.Types.CtLoc
#endif

#ifdef TIMING
import GHC.Clock
#endif

#if __GLASGOW_HASKELL__ <= 904
type Subst = TCvSubst

isEmptySubst :: Subst -> Bool
isEmptySubst = isEmptyTCvSubst
#endif

data EffGiven = EffGiven
  { effCon :: Type
  , eff :: Type
  , es :: Type
  }

data EffWanted = EffWanted
  { effCon :: Type
  , eff :: Type
  , es :: Type
  , loc :: CtLoc
  }

newtype OtherGiven = OtherGiven
  { ty :: Type
  }

data OtherWanted = OtherWanted
  { ty :: Type
  , vars :: TyCoVarSet
  }

data Candidates a = None | Single a | Multiple

type EffCandidates = Candidates EffGiven

----------------------------------------

data PluginData = PluginData
  { elemClass :: Class
  , downClass :: Class
  , downTailClass :: Class
  , totalTime :: !(IORef Double)
  }

plugin :: Plugin
plugin = defaultPlugin
  { tcPlugin = \_ -> Just TcPlugin
    { tcPluginInit = initPlugin
#if __GLASGOW_HASKELL__ > 902
    , tcPluginRewrite = \_ -> emptyUFM
#endif
    , tcPluginSolve = disambiguateAll
    , tcPluginStop = pluginStopHook
    }
  , pluginRecompile = purePlugin
  }

initPlugin :: TcPluginM PluginData
initPlugin = do
  clsMod <- lookupModule $ mkModuleName "Control.Effect.Internal.Effs.Sum"
  elemClass <- tcLookupClass =<< lookupOrig clsMod (mkTcOcc "Member")
  downMod <- lookupModule $ mkModuleName "Control.Effect.CodeGen.Down"
  downClass <- tcLookupClass =<< lookupOrig downMod (mkTcOcc "$~>")
  downTailClass <- tcLookupClass =<< lookupOrig downMod (mkTcOcc "$~>>")
  totalTime <- tcPluginIO $ newIORef 0
  pure PluginData{..}
  where
    lookupModule :: ModuleName -> TcPluginM Module
    lookupModule modName = do
      hscEnv <- getTopEnv
      findPluginModuleCompat hscEnv modName >>= \case
        Found _ md -> pure md
        _ -> errorWithoutStackTrace ("effective-plugin: can't find module " ++ show modName)

#if __GLASGOW_HASKELL__ == 902

type TcPluginSolveResult = TcPluginResult

(|>) :: TcPluginSolveResult -> TcPluginSolveResult -> TcPluginSolveResult
TcPluginOk ys zs |> TcPluginOk ys' zs' = TcPluginOk (ys ++ ys') (zs ++ zs')
r1 |> r2 = r1

mkSolveResult :: [Ct] -> TcPluginSolveResult 
mkSolveResult xs = TcPluginOk [] xs

#else

(|>) :: TcPluginSolveResult -> TcPluginSolveResult -> TcPluginSolveResult
(TcPluginSolveResult xs ys zs) |> (TcPluginSolveResult xs' ys' zs') =
    TcPluginSolveResult (xs ++ xs') (ys ++ ys') (zs ++ zs')

mkSolveResult :: [Ct] -> TcPluginSolveResult 
mkSolveResult xs = TcPluginSolveResult [] [] xs

#endif

#if __GLASGOW_HASKELL__ == 902
disambiguateAll
  :: PluginData
  -> [Ct]
  -> [Ct]
  -> [Ct]
  -> TcPluginM TcPluginSolveResult
disambiguateAll pd allGivens _ allWanteds = timed pd $ do

#else

disambiguateAll
  :: PluginData
  -> EvBindsVar
  -> [Ct]
  -> [Ct]
  -> TcPluginM TcPluginSolveResult
disambiguateAll pd _ allGivens allWanteds = timed pd $ do
#endif

  r1 <- resolveEagerly pd pd.downClass allGivens allWanteds
  r2 <- resolveEagerly pd pd.downTailClass allGivens allWanteds
  r3 <- disambiguateEffects pd allGivens allWanteds
  return (r1 |> (r2 |> r3))

-- | If there is no instance matching the wanted constraint but a unique instance
-- that can be unified with the wanted constraint, we commit to this instance eagerly.
--
-- For exmaple, the wanted constraint may be @StateT s Gen $~> StateT s' Identity@
-- for some unification variables @s@ and @s'@, and it doesn't match the instance 
-- @StateT (Up s) n $~> StateT s m@, but this instance is likely to be the only 
-- instance that can be unified with the wanted constraint. In this case we commit 
-- to this instance by generating equality constraints that @s@ and @s'@  
-- must be @Up t@ and @t'@ for some fresh unification variable t and t'.
resolveEagerly
  :: PluginData
  -> Class
  -> [Ct]
  -> [Ct]
  -> TcPluginM TcPluginSolveResult
resolveEagerly pd cls allGivens allWanteds = timed pd $ do
  let wanteds :: [(CtLoc, [Type])]
      wanteds = mapMaybe (wantedIsCls cls) . filter (not . isIP) $ allWanteds
  instEnvs <- getInstEnvs
  cts <- forM wanteds $ \wanted -> do
    printSingle "Wanted" wanted
    case lookupInstEnv False instEnvs cls (snd wanted) of
#if __GLASGOW_HASKELL__ == 902
      ([], [uniqUnifyingInst], []) ->
#elif __GLASGOW_HASKELL__ == 904 || __GLASGOW_HASKELL__ == 906
      ([], OneOrMoreUnifiers [uniqUnifyingInst], []) ->
#else
      ([], OneOrMoreUnifiers (uniqUnifyingInst :| []), []) ->
#endif
        do let (vars, _, tys) = instanceHead uniqUnifyingInst
           vars' <- forM vars (\v -> newFlexiTyVar (tyVarKind v))
           let 
#if __GLASGOW_HASKELL__ < 906
               sub = extendTvSubstList  emptyTCvSubst vars (map mkTyVarTy vars')
#else
               sub = extendTvSubstList emptySubst (zipWith (\v v' -> (v, mkTyVarTy v')) vars vars')
#endif
               tys' = map (substTy sub) tys
#if __GLASGOW_HASKELL__ <= 912
               cs = zipWith mkPrimEqPred (snd wanted) tys'
#else
               cs = zipWith mkNomEqPred (snd wanted) tys'
#endif
           es <- forM cs (newWanted (fst wanted))
           return (map mkNonCanonical es) 
      _ -> pure []
  pure (mkSolveResult (concat cts))

disambiguateEffects
  :: PluginData
  -> [Ct]
  -> [Ct]
  -> TcPluginM TcPluginSolveResult
disambiguateEffects pd allGivens allWanteds = timed pd $ do
  printList "Givens" allGivens
  printList "EffGivens" effGivens
  printList "OtherGivens" otherGivens
  printList "Wanteds" allWanteds
  printList "EffWanteds" effWanteds
  printList "OtherWanteds" otherWanteds
  instEnvs <- getInstEnvs
  solutions <- tcPluginIO $ newIORef []
  forM_ effWanteds $ \wanted -> do
    printSingle "Wanted" wanted
    case findCandidates wanted effGivens of
      Left given -> printSingle "Already solved by" given
      Right [] -> printLn "No candidates"
      Right [(given, _)] -> do
        printSingle "Single candidate found" given
        emitEqConstraint solutions wanted given
      Right candidates -> do
        printList "Multiple candidates found" $ map fst candidates
        filterCandidates instEnvs None candidates >>= \case
          None -> printLn "No candidates left"
          Single given -> do
            printSingle "Single candidate left" given
            emitEqConstraint solutions wanted given
          Multiple -> printLn "Multiple candidates left"
  printLn ""
  mkSolveResult <$> tcPluginIO (readIORef solutions)
  where
    (otherGivens, effGivens)
      = second (extendEffGivens effWanteds)
      . partitionEithers
      . map (groupGivens pd.elemClass)
      . filter (not . isIP)
      $ allGivens

    (otherWanteds, effWanteds)
      = partitionEithers
      . map (groupWanteds pd.elemClass)
      . filter (not . isIP)
      $ allWanteds

    filterCandidates
      :: InstEnvs
      -> EffCandidates
      -> [(EffGiven, Subst)]
      -> TcPluginM EffCandidates
    filterCandidates instEnvs acc = \case
      [] -> pure acc
      (given, subst) : rest -> do
        printSingle "Candidate" given
        let relevantWanteds = (`mapMaybe` otherWanteds) $ \wanted ->
              if substHasAnyTyVar subst wanted.vars
              then Just $ substTy subst wanted.ty
              else Nothing
        printList "Relevant wanteds" relevantWanteds
        allWantedsSolvable relevantWanteds >>= \case
          True -> do
            printLn "Candidate fits"
            case acc of
              None -> filterCandidates instEnvs (Single given) rest
              Single _ -> pure Multiple
              Multiple -> error "unreachable"
          False -> do
            printLn "Candidate doesn't fit, skipping"
            filterCandidates instEnvs acc rest
      where
        allWantedsSolvable :: [Type] -> TcPluginM Bool
        allWantedsSolvable = \case
          [] -> pure True
          wanted : rest -> do
            printSingle "Checking" wanted
            if wanted `unifiesWithAny` otherGivens
              then do
                printLn "Solvable from local context"
                allWantedsSolvable rest
              else case tcSplitTyConApp wanted of
                (con, args) -> case tyConClass_maybe con of
                  Nothing -> do
                    printLn "Not a class constraint"
                    pure False
                  Just cls -> case lookupInstEnv False instEnvs cls args of
                    ([], _, _) -> do
                      printLn "No matching instances found"
                      pure False
                    _ -> do
                      printLn "Found matching instances"
                      allWantedsSolvable rest

----------------------------------------
-- Standalone helpers

findPluginModuleCompat :: HscEnv -> ModuleName -> TcPluginM FindResult
findPluginModuleCompat hsc_env mod_name = do
#if __GLASGOW_HASKELL__ <= 912 && __GLASGOW_HASKELL__ > 902
  let dflags = hsc_dflags hsc_env
      fopts = initFinderOpts dflags
      fc = hsc_FC hsc_env
      units = hsc_units hsc_env
      home_unit = hsc_home_unit hsc_env
  tcPluginIO (findPluginModule fc fopts units (Just home_unit) mod_name)
#else
  tcPluginIO (findPluginModule hsc_env mod_name)
#endif

-- | Record a wanted equality constraint to aid typechecking.
emitEqConstraint :: IORef [Ct] -> EffWanted -> EffGiven -> TcPluginM ()
emitEqConstraint solutions wanted given = do
  let predTy =
#if __GLASGOW_HASKELL__ <= 912
        mkPrimEqPred wanted.eff given.eff
#else
        mkNomEqPred wanted.eff given.eff
#endif
  printSingle "Emitting constraint" predTy
  ev <- newWanted wanted.loc predTy
  tcPluginIO $ modifyIORef' solutions (mkNonCanonical ev :)

-- | Separate givens based on whether they're of the form @e :> es@ or not.
groupGivens :: Class -> Ct -> Either OtherGiven EffGiven
groupGivens elemCls = \case
#if __GLASGOW_HASKELL__ < 908
  CDictCan
    { cc_class = cls
    , cc_tyargs = [eff, es]
    }
    | cls == elemCls ->
#else
  CDictCan DictCt
    { di_cls = cls
    , di_tys = [eff, es]
    }
    | cls == elemCls ->
#endif
    Right EffGiven
      { effCon = fst $ splitAppTys eff
      , eff = eff
      , es = es
      }
  ct -> Left OtherGiven
    { ty = ctPred ct
    }

-- | Separate wanteds based on whether they're of the form @e :> es@ or not.
groupWanteds :: Class -> Ct -> Either OtherWanted EffWanted
groupWanteds elemCls = \case
#if __GLASGOW_HASKELL__ < 908
  CDictCan
    { cc_ev = CtWanted { ctev_loc = loc }
    , cc_class = cls
    , cc_tyargs = [eff, es]
    }
    | cls == elemCls ->
#elif __GLASGOW_HASKELL__ <= 912
  CDictCan DictCt
    { di_ev = CtWanted { ctev_loc = loc }
    , di_cls = cls
    , di_tys = [eff, es]
    }
    | cls == elemCls ->
#else
  CDictCan DictCt
    { di_ev = CtWanted WantedCt { ctev_loc = loc }
    , di_cls = cls
    , di_tys = [eff, es]
    }
    | cls == elemCls ->
#endif
    Right EffWanted
      { effCon = fst $ splitAppTys eff
      , eff = eff
      , es = es
      , loc = loc
      }
  ct ->
    Left OtherWanted
      { ty = ctPred ct
      , vars = tyCoVarsOfType $ ctPred ct
      }


-- | Test if a wanted constraint is of the form `elemCls args...`.
-- If so, return its location and its list of arguments. 
wantedIsCls :: Class -> Ct -> Maybe (CtLoc, [Type])
wantedIsCls elemCls = \case
#if __GLASGOW_HASKELL__ < 908
  CDictCan
    { cc_ev = CtWanted { ctev_loc = loc }
    , cc_class = cls
    , cc_tyargs = args
    }
    | cls == elemCls ->
#elif __GLASGOW_HASKELL__ <= 912
  CDictCan DictCt
    { di_ev = CtWanted { ctev_loc = loc }
    , di_cls = cls
    , di_tys = args
    }
    | cls == elemCls ->
#else
  CDictCan DictCt
    { di_ev = CtWanted WantedCt { ctev_loc = loc }
    , di_cls = cls
    , di_tys = args
    }
    | cls == elemCls ->
#endif
    Just (loc, args) 
  ct ->
    Nothing

-- | We don't get appropriate given constraints when dealing with concrete (or
-- partially concrete) effect lists like (A : B : C : es), so they need to be
-- manually added (GHC will resolve them later).
extendEffGivens :: [EffWanted] -> [EffGiven] -> [EffGiven]
extendEffGivens wanteds givens = loop givens . nubType $ map (.es) wanteds
  where
    loop :: [EffGiven] -> [Type] -> [EffGiven]
    loop acc = \case
      [] -> acc
      fullEs : rest ->
        let extractGivens :: Type -> [EffGiven]
            extractGivens es = case splitAppTys es of
              (_colon, [_kind, eff, esTail]) -> EffGiven
                { effCon = fst $ splitAppTys eff
                , eff = eff
                , es = fullEs
                } : extractGivens esTail
              _ -> []
        in loop (extractGivens fullEs ++ acc) rest

-- | Check if a constraint in an implicit parameter. We discard all of them
-- since they will not affect resolution of @:>@ constraints.
isIP :: Ct -> Bool
isIP = \case
#if __GLASGOW_HASKELL__ < 908
  CDictCan { cc_class = cls } -> isIPClass cls
#else
  CDictCan DictCt { di_cls = cls } -> isIPClass cls
#endif
  _ -> False

-- | Attempt to unify types, but skip skolem (rigid) type variables. This is
-- crucial for proper filtering of candidates.
tcUnifyTyNoSkolems :: Type -> Type -> Maybe Subst
tcUnifyTyNoSkolems ty1 ty2 = tcUnifyTys bindFun [ty1] [ty2]
  where
    bindFun var _ty = if isSkolemTyVar var then dontBindMe else BindMe

    dontBindMe =
#if __GLASGOW_HASKELL__ <= 912
      Apart
#else
      DontBindMe
#endif

unifiesWithAny :: Type -> [OtherGiven] -> Bool
unifiesWithAny ty = any (isJust . tcUnifyTyNoSkolems ty . (.ty))

substHasAnyTyVar :: Subst -> TyCoVarSet -> Bool
substHasAnyTyVar subst = uniqSetAny (`elemUFM` getTvSubstEnv subst)

-- | Find givens unifiable with a wanted and give them back along with
-- appropriate substitutions.
--
-- Returns Left if the wanted is already solved by one of the givens.
findCandidates :: EffWanted -> [EffGiven] -> Either EffGiven [(EffGiven, Subst)]
findCandidates wanted = loop []
  where
    loop acc = \case
      [] -> Right acc
      given : rest ->
        if wanted.effCon `eqType` given.effCon && wanted.es `eqType` given.es
        then case tcUnifyTyNoSkolems wanted.eff given.eff of
          Just subst
            | isEmptySubst subst -> Left given
            | otherwise -> loop ((given, subst) : acc) rest
          Nothing -> loop acc rest
        else loop acc rest

{-
findDownCandidates :: EffWanted -> [EffGiven] -> Either EffGiven [(EffGiven, Subst)]
findDownCandidates wanted = loop []
  where
    loop acc = \case
      [] -> Right acc
      given : rest ->
        case case tcUnifyTyNoSkolems wanted.eff given.eff



        if wanted.effCon `eqType` given.effCon && wanted.es `eqType` given.es
        then case tcUnifyTyNoSkolems wanted.eff given.eff of
          Just subst
            | isEmptySubst subst -> Left given
            | otherwise -> loop ((given, subst) : acc) rest
          Nothing -> loop acc rest
        else loop acc rest
-}

nubType :: [Type] -> [Type]
nubType = coerce . S.toList . S.fromList @OrdType . coerce

newtype OrdType = OrdType Type

instance Eq OrdType where
  (==) = coerce eqType

instance Ord OrdType where
  compare = coerce nonDetCmpType

----------------------------------------
-- Debugging

#ifdef TIMING

timed :: PluginData -> TcPluginM a -> TcPluginM a
timed pd action = do
  t1 <- tcPluginIO getMonotonicTime
  a <- action
  tcPluginIO $ do
    t2 <- getMonotonicTime
    modifyIORef' pd.totalTime (+ (t2 - t1))
  pure a

pluginStopHook :: PluginData -> TcPluginM ()
pluginStopHook pd = tcPluginIO $ do
  time <- readIORef pd.totalTime
  putStrLn $ "Execution time of effectful-plugin (seconds): " ++ show time

#else

timed :: PluginData -> TcPluginM a -> TcPluginM a
timed _ action = action

pluginStopHook :: PluginData -> TcPluginM ()
pluginStopHook _ = pure ()

#endif


#ifdef VERBOSE

showOut :: O.Outputable o => o -> String
showOut = O.showSDocOneLine O.defaultSDocContext . O.ppr

printSingle :: O.Outputable x => String -> x -> TcPluginM ()
printSingle header x = printLn $ header ++ ": " ++ showOut x

printList :: O.Outputable x => String -> [x] -> TcPluginM ()
printList header = \case
  [] -> printLn $ header ++ ": []"
  xs -> do
    printLn $ header ++ ":"
    forM_ xs $ \x -> printLn $ "- " ++ showOut x

printLn :: String -> TcPluginM ()
printLn = tcPluginIO . putStrLn

#else

printSingle :: String -> x -> TcPluginM ()
printSingle _ _ = pure ()

printList :: String -> [x] -> TcPluginM ()
printList _ _ = pure ()

printLn :: String -> TcPluginM ()
printLn _ = pure ()

#endif

-- Instances for outputting
--------------------------------------------------------------------------------

instance O.Outputable EffWanted where
  ppr wanted =
    O.text "[W]" O.<+> O.ppr wanted.eff O.<+> O.text ":>" O.<+> O.ppr wanted.es

instance O.Outputable EffGiven where
  ppr given =
    O.text "[G]" O.<+> O.ppr given.eff O.<+> O.text ":>" O.<+> O.ppr given.es

instance O.Outputable OtherGiven where
  ppr given =
    O.text "[G]" O.<+> O.ppr given.ty

instance O.Outputable OtherWanted where
  ppr wanted =
    O.text "[W]" O.<+> O.ppr wanted.ty