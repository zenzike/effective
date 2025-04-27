{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Handlers where

import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.GenM

import Control.Effect
import Control.Effect.State
import Control.Effect.Family.Algebraic
import Data.Functor.Identity
import Data.Iso
import Data.HFunctor

letPut :: Handler '[Put (Up s)] '[Put (Up s), CodeGen] '[] '[]
letPut = interpret1 (\(Alg (Put s k)) -> do s' <- genLet s; put s'; return k) 

genAlg :: Algebra [CodeGen, UpOp Identity] Gen 
genAlg o
  | Just (Alg o) <- prj @CodeGen o    = o
  | Just up <- prj @(UpOp Identity) o = bwd upIso (\cm -> return [||runIdentity $$cm||]) up

genMAlg :: forall m. Monad m => Algebra '[CodeGenM m, CodeGen, UpOp m] (GenM m)
genMAlg o 
  | Just (Alg o) <- prj @(CodeGenM _) o = o
  | Just (Alg o) <- prj @CodeGen      o = specialise o
  | Just up      <- prj @(UpOp m) o     = bwd upIso genDo_ up