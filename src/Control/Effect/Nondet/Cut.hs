{-|
Module      : Control.Effect.Cut
Description : Nondeterminism with a cut operation
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides an effect for nondeterminism with a cut operation.
The cut operation allows for pruning the search space in nondeterministic computations.
-}

module Control.Effect.Nondet.Cut where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Nondet.Operations
import Control.Monad.Trans.CutList
{-
Idea:

Nondeterminism consists of just or and stop.
A model of this is lists, using the list monad transformer.

If we want a notion of backtracking, we must include
a new operation, like `try`, which can be interpreted
as executing `once`, many times etc.

One way to interpret `once` is into the list monad directly.
An alternative is to interpret `once` into `cutFail` and `cutCall`,
which can then be interpreted using a `CutList`.
-}

-- | The `cutListAlg` function defines the algebra for handling the t`CutListT` monad transformer.
-- It clears the `cut` at the boundary of a `cutCall`.
cutListAlg
  :: Monad m => Algebra [Empty, Choose, NondetOr, CutFail, CutCall] (CutListT m)
cutListAlg =
  (\Empty -> empty) :#
  (\(Choose xs ys) -> xs <|> ys) :#
  (\(NondetOr xs ys) -> return xs <|> return ys) :#
  (\CutFail -> CutListT (\cons nil zero -> zero)) :#.
  (\(CutCall xs) -> CutListT (\cons nil zero -> runCutListT xs cons nil nil))

-- | An algebra transformer based on t`CutListT`.
cutListAT :: AlgTrans [Empty, Choose, NondetOr, CutFail, CutCall] '[] '[CutListT] Monad
cutListAT = algTrans' cutListAlg

-- | A handler for the t`CutListT` monad transformer.
cutList :: Handler [Empty, Choose, NondetOr, CutFail, CutCall] '[] '[CutListT] a [a]
cutList = handler' fromCutListT cutListAlg

-- | A handler for the @Once@ effect using @CutCall@ and @CutFail@.
onceCut :: Handler '[Once] '[CutCall, CutFail, Empty, Choose] '[] a a
onceCut = interpretM onceCutAlg

-- | Transforming the operation @Once@ to @CutCall@, @CutFail@, and @Choose@.
onceCutAT :: AlgTrans '[Once] '[CutCall, CutFail, Empty, Choose] '[] Monad
onceCutAT = AlgTrans onceCutAlg

-- | The algebra for handling the @Once@ effect with @CutCall@ and @CutFail@.
onceCutAlg
  :: forall m.
     Monad m
  => Algebra [CutCall, CutFail, Empty, Choose] m
  -> Algebra '[Once] m
onceCutAlg oalg = singAlg $ \(Once p) -> cutCallM oalg $
  do x <- p
     eval oalg cut
     return x

-- | A combined handler for @Once@, @Empty@, @Choose@, @CutFail@, and @CutCall@ effects.
onceNondet :: Handler '[Once, Empty, Choose, NondetOr, CutFail, CutCall] '[] '[CutListT] a [a]
onceNondet = onceCut |> cutList