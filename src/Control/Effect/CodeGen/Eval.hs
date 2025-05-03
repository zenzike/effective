{-# LANGUAGE TemplateHaskell, MonoLocalBinds #-}
module Control.Effect.CodeGen.Eval where

import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.GenM

import Control.Effect
import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.Forward.ForwardC as F
import Control.Effect.State
import Control.Effect.Family.Algebraic
import Data.Functor.Identity
import Data.Iso
import Data.HFunctor
import Data.List.Kind

putUp :: Member (Put (Up c)) sig => Up c -> Prog sig ()
putUp c = put c 

getUp :: Member (Get (Up c)) sig => Prog sig (Up c)
getUp = get

letPut :: forall s. AlgTransM '[Put (Up s)] '[Put (Up s), CodeGen] '[] 
letPut = interpretAT1 (\(Alg (Put s k)) -> do s' <- genLet s; put s'; return k) 

genAlg :: Algebra [CodeGen, UpOp Identity] Gen 
genAlg o
  | Just (Alg o) <- prj @CodeGen o    = o
  | Just up <- prj @(UpOp Identity) o = bwd upIso (\cm -> return [||runIdentity $$cm||]) up

genMAlg :: forall m. Monad m => Algebra '[CodeGenM m, CodeGen, UpOp m] (GenM m)
genMAlg o 
  | Just (Alg o) <- prj @(CodeGenM _) o = o
  | Just (Alg o) <- prj @CodeGen      o = specialise o
  | Just up      <- prj @(UpOp m) o     = bwd upIso genDo_ up

type GenEffects = [CodeGen, UpOp Identity]

type AutoEvalGen effs oeffs = 
  ( HFunctor (Effs (effs `Union` GenEffects))
  , AutoWithFwds effs oeffs GenEffects )

evalGen :: forall effs oeffs ts cs a. 
           ( cs Gen
           , Monad (Apply ts Gen)
           , F.Forwards cs GenEffects ts
           , Injects (oeffs `Union` GenEffects) GenEffects 
           , AutoEvalGen effs oeffs )
        => AlgTrans effs oeffs ts cs 
        -> Prog (effs `Union` GenEffects) a -> Apply ts Gen a
evalGen at = evalTr genAlg (withFwds @[CodeGen, UpOp Identity] at)

type GenMEffects m = [CodeGenM m, CodeGen, UpOp m]

type AutoEvalGenM effs oeffs m = 
  ( HFunctor (Effs (effs `Union` GenMEffects m))
  , AutoWithFwds effs oeffs (GenMEffects m) )

evalGenM :: forall m effs oeffs ts cs a. 
            ( cs (GenM m), Monad m
            , Monad (Apply ts (GenM m))
            , F.Forwards cs (GenMEffects m) ts
            , Injects (oeffs `Union` GenMEffects m) (GenMEffects m)
            , AutoEvalGenM effs oeffs m )
         => AlgTrans effs oeffs ts cs
         -> Prog (effs `Union` GenMEffects m) a -> Apply ts (GenM m) a
evalGenM at = evalTr (genMAlg @m) (withFwds @(GenMEffects m) at)