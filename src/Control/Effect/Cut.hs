{-|
Module      : Control.Effect.Cut
Description : Nondeterminism with a cut operation
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides an effect for nondeterminism with a cut operation.
The cut operation allows for pruning the search space in nondeterministic computations.
-}

module Control.Effect.Cut where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Alternative
import Control.Effect.Nondet
import Control.Monad.Trans.CutList

{-
Idea:

Nondeterminism consists of just or and stop.
A model of this is lists, using the list monad transformer.

If we want a notion of backtracking, we must include
a new operation, like `try`, which can be interpreted
as executing `once`, many times etc.

One way to interpret `once` is into the list monad directly.
An alternative is to interpet `once` into `cutFail` and `cutCall`,
which can then be interpreted using a `CutList`.
-}

-- | Signature for t`CutFail`, which fails and cuts all following nondeterministic
-- siblings.
$(makeAlg [e| cutFail :: 0 |])

-- | The t`CutCall` effect represents a scoped computation with a cut boundary.
$(makeScp [e| cutCall :: 1 |])

-- | Perform a cut operation, pruning the search space.
cut :: (Members [Empty, Choose, CutFail] sig) => Prog sig ()
cut = skip <|> cutFail

-- | A no-op computation that does nothing.
skip :: Monad m => m ()
skip = return ()

-- | The `cutListAlg` function defines the algebra for handling the t`CutListT` monad transformer.
-- It clears the `cut` at the boundary of a `cutCall`.
cutListAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> forall x. Effs [Empty, Choose, CutFail, CutCall] (CutListT m) x -> CutListT m x
cutListAlg oalg Empty          = empty
cutListAlg oalg (Choose xs ys) = xs <|> ys
cutListAlg oalg CutFail        = CutListT (\cons nil zero -> zero)
cutListAlg oalg (CutCall xs)   = CutListT (\cons nil zero -> runCutListT xs cons nil nil)

cutListAT :: AlgTrans [Empty, Choose, CutFail, CutCall] '[] '[CutListT] Monad
cutListAT = AlgTrans cutListAlg

-- | A handler for the t`CutListT` monad transformer.
cutList :: Handler [Empty, Choose, CutFail, CutCall] '[] '[CutListT] a [a]
cutList = handler' fromCutListT cutListAlg

-- | A handler for the t`Once` effect using t`CutCall` and t`CutFail`.
onceCut :: Handler '[Once] '[CutCall, CutFail, Empty, Choose] '[] a a
onceCut = interpretM onceCutAlg

-- | Transforming the operation t`Once` to t`CutCall`, t`CutFail`, and `Choose`.
onceCutAT :: AlgTrans '[Once] '[CutCall, CutFail, Empty, Choose] '[] Monad
onceCutAT = AlgTrans onceCutAlg

-- | The algebra for handling the t`Once` effect with t`CutCall` and t`CutFail`.
onceCutAlg :: forall m .
     Monad m
  => (forall x. Effs '[CutCall, CutFail, Empty, Choose] m x -> m x)
  -> (forall x. Effs '[Once] m x -> m x)
onceCutAlg oalg (Once p) = cutCallM oalg $
  do x <- p
     eval oalg cut
     return x

-- | A combined handler for t`Once`, t`Empty`, t`Choose`, t`CutFail`, and t`CutCall` effects.
onceNondet :: Handler '[Once, Empty, Choose, CutFail, CutCall] '[] '[CutListT] a [a]
onceNondet = onceCut |> cutList
