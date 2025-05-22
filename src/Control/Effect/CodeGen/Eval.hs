{-|
Module      : Control.Effect.CodeGen.Eval
Description : Evaluating meta-programs into object-level code
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains functions for evaluating meta-programs into object-level 
programs. The function `stage` is probably the most useful one.
-}

{-# LANGUAGE TemplateHaskell, MonoLocalBinds, MagicHash #-}
module Control.Effect.CodeGen.Eval where

import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Down

import Control.Effect
import Control.Effect.Internal.AlgTrans
import Control.Effect.Family.Algebraic
import Data.Functor.Identity
import Data.Iso
import Data.HFunctor
import Data.List.Kind

-- | The effects supported by the monad `Gen`.
type GenEffects = [CodeGen, UpOp Identity]

-- | The algebra of `Gen`.
genAlg :: Algebra GenEffects Gen 
genAlg o
  | Just (Alg o) <- prj @CodeGen o    = o
  | Just up <- prj @(UpOp Identity) o = bwd upIso (\cm -> return [||runIdentity $$cm||]) up

-- | The effects supported by the monad `GenM m`.
type GenMEffects m = [CodeGenM m, CodeGen, UpOp m]

-- | The algebra on `GenM`.
genMAlg :: forall m. Monad m => Algebra (GenMEffects m) (GenM m)
genMAlg o 
  | Just (Alg o) <- prj @(CodeGenM _) o = o
  | Just (Alg o) <- prj @CodeGen      o = specialise o
  | Just up      <- prj @(UpOp m) o     = bwd upIso genDo_ up


type EvalGen# effs oeffs = 
  ( HFunctor (Effs (effs `Union` GenEffects))
  , WithFwds# effs oeffs GenEffects )

-- | Evaluate a program with an algebra transformer, with `Gen` at the bottom
-- of monad transformer stack.
evalGen :: forall effs oeffs ts cs a. 
           ( cs Gen
           , Monad (Apply ts Gen)
           , ForwardsC ((~) Gen) GenEffects ts
           , Injects (oeffs `Union` GenEffects) GenEffects 
           , EvalGen# effs oeffs )
        => AlgTrans effs oeffs ts cs 
        -> Prog (effs `Union` GenEffects) a -> Apply ts Gen a
evalGen at = evalTr genAlg (withFwds (Proxy @GenEffects) (weakenC @((~) Gen) at))

-- | Stage a meta-level program into an object-level monadic computation via `Gen`.
stage :: forall m effs oeffs ts cs a. 
         ( cs Gen
         , Monad (Apply ts Gen)
         , ForwardsC ((~) Gen) GenEffects ts
         , Injects (oeffs `Union` GenEffects) GenEffects 
         , Apply ts Gen $~> m
         , EvalGen# effs oeffs )
      => AlgTrans effs oeffs ts cs 
      -> Prog (effs `Union` GenEffects) (Up a) 
      -> Up (m a)
stage alg = down . evalGen alg

type EvalGenM# effs oeffs m = 
  ( HFunctor (Effs (effs `Union` GenMEffects m))
  , WithFwds# effs oeffs (GenMEffects m) )

-- | Evaluate a program with an algebra transformer, with `GenM m` at the bottom
-- of monad transformer stack.
evalGenM :: forall m effs oeffs ts cs a. 
            ( cs (GenM m), Monad m
            , Monad (Apply ts (GenM m))
            , ForwardsC ((~) (GenM m)) (GenMEffects m) ts
            , Injects (oeffs `Union` GenMEffects m) (GenMEffects m)
            , EvalGenM# effs oeffs m )
         => AlgTrans effs oeffs ts cs
         -> Prog (effs `Union` GenMEffects m) a -> Apply ts (GenM m) a
evalGenM at = evalTr genMAlg (withFwds (Proxy @(GenMEffects m)) (weakenC @((~) (GenM m)) at))

-- | Stage a meta-level program into an object-level monadic computation via `GenM`.
stageM :: forall m m' effs oeffs ts cs a. 
            ( cs (GenM m), Monad m
            , Monad (Apply ts (GenM m))
            , ForwardsC ((~) (GenM m)) (GenMEffects m) ts
            , Injects (oeffs `Union` GenMEffects m) (GenMEffects m)
            , Apply ts (GenM m) $~> m' 
            , EvalGenM# effs oeffs m )
         => Proxy m
         -> AlgTrans effs oeffs ts cs
         -> Prog (effs `Union` GenMEffects m) (Up a) 
         -> Up (m' a)
stageM _ at = down . evalGenM @m at