{-|
Module      : Control.Effect.Nondet
Description : Effects for nondeterminism
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental

This module provides nondeterministic operations and handlers. The interface
for nondeterminism in @effective@ is a bit subtle. We have the following operations:

  1. t`Choose` and t`Empty` directly correspond to the `Alternative` typeclass
     of GHC, and there is an instance

     @
       instance (Member Empty effs, Member Choose effs) => Alternative (Prog effs) where ...
     @

     Moreover, t`Choose` is a binary scoped operation because `Alternative` does not require
     distributivity of @>>=@ over t`Choose`.

  2. t`NondetOr` is also a nondeterministic choice, but it is an /algebraic/ operation.
     t`Once` is a unary scoped operation, which keeps only the first result of a computation.

  3. t`CutFail` fails the computation and also stops exploring more nondeterministic branches.
     t`CutCall` is a unary scoped operation that delimits the scope that t`CutFail` affects.
     Using these two operations, a `cut` operation in the style of Prolog can be implemented.

These operations have the following handlers:

  1. t`Choose` and t`Empty` are handled using `Control.Effect.Nondet.Alternative.alternative`
     or its specialisations, such as `list` and `Control.Effect.Nondet.Alternative.logic`.

  2. t`NondetOr` and t`Once`, together with the operations above, are handled
     using handlers from "Control.Effect.Nondet.List" or
     "Control.Effect.Nondet.LogicT". These two modules implement the same interface
     and the only difference is that one of them is based on `ListT` while the
     other is based on `Control.Effect.Nondet.Logic.LogicT`.

  3. t`CutFail` and t`CutCall`, together with the operations above, are handled using handlers
     from the module "Control.Effect.Nondet.Cut" based on a variation of @LogicT@
     defined in "Control.Monad.Trans.CutList".

The current module re-exports only the handlers from "Control.Effect.Nondet.Alternative". If you
need handlers of other operations, you can import the modules in @Control/Effect/Nondet/@.
-}

module Control.Effect.Nondet
  ( module Control.Effect.Nondet.Alternative) where

import Control.Effect.Nondet.Alternative