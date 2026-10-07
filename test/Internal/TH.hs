{-# LANGUAGE TemplateHaskell #-}

{-|
Module      : Internal.TH
Description : Tests of the Template Haskell helpers
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental

The helpers of "Control.Effect.Internal.TH" generate an operation and its
smart constructors from a signature or from a functor. The test is that this
module compiles: each splice is followed by the generated constructors at the
types that the helpers are meant to give them.
-}
module Internal.TH (tests) where

import Prelude hiding (flip)

import Control.Effect
import Control.Effect.WithName
import Control.Effect.Internal.TH

import Test.Tasty

tests :: TestTree
tests = testGroup "TH" []

-- An algebraic operation from a signature: a parameter and two continuations.
$(makeAlg [e| flip :: Float ~> 2 |])

flip' :: Member Flip effs => Float -> Prog effs x -> Prog effs x -> Prog effs x
flip' = flip

flipP' :: Member (WithName name Flip) effs
       => Proxy name -> Float -> Prog effs x -> Prog effs x -> Prog effs x
flipP' = flipP

#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
flipN' :: forall name -> Member (WithName name Flip) effs
       => Float -> Prog effs x -> Prog effs x -> Prog effs x
flipN' name = flipN name
#endif

-- An algebraic operation from its functor.
data MyOp_ s k = MyOp_ k s k deriving Functor
$(makeAlgFrom ''MyOp_)

myOp' :: Member (MyOp s) effs => Prog effs x -> s -> Prog effs x -> Prog effs x
myOp' = myOp

-- A scoped operation from a signature.
$(makeScp [e| tryCatch :: 2 |])

tryCatch' :: Member TryCatch effs => Prog effs x -> Prog effs x -> Prog effs x
tryCatch' = tryCatch

tryCatchM' :: Member TryCatch effs => Algebra effs m -> m x -> m x -> m x
tryCatchM' = tryCatchM

tryCatchP' :: Member (WithName name TryCatch) effs
           => Proxy name -> Prog effs x -> Prog effs x -> Prog effs x
tryCatchP' = tryCatchP
