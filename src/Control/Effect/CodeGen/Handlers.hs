module Control.Effect.CodeGen.Handlers where

import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Gen

import Control.Effect
import Control.Effect.State
import Control.Effect.Algebraic

letPut :: Handler '[Put (Up s)] '[Put (Up s), LiftGen] IdentityT Identity
letPut = interpret1 (\(Alg (Put s k)) -> do s' <- genLet s; put s'; return k) 

genAlg :: Algebra [Alg Gen, UpOp Identity] Gen 
genAlg = liftGenAlg # upGenAlg