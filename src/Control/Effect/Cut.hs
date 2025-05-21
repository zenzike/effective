{-|
Module      : Control.Effect.Cut
Description : Nondeterminism with a cut operation
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Cut where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Alternative
import Control.Effect.Nondet
import Control.Monad.Trans.CutList.CPS
import Data.HFunctor ( HFunctor(..) )

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

type CutFail = Alg CutFail_
data CutFail_ a where
  CutFail :: CutFail_ a
  deriving Functor

cutFail :: Member CutFail sig => Prog sig a
cutFail = call (Alg CutFail)

type CutCall = Scp CutCall_
data CutCall_ a where
  CutCall :: a -> CutCall_ a
  deriving Functor

cut :: (Members [Choose, CutFail] sig) => Prog sig ()
cut = or skip cutFail

cutCall :: Member CutCall sig => Prog sig a -> Prog sig a
cutCall p = call' (Scp (CutCall p))

cutCallM :: (Monad m, Member CutCall sig)
  => (forall a . Effs sig m a -> m a) -> m a -> m a
cutCallM alg p = (alg . inj) (Scp (CutCall p))

skip :: Monad m => m ()
skip = return ()

-- | The `cutListAlg` will clear the `cut` at the boundary of a `cutCall`.
cutListAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> forall x. Effs [Empty, Choose, CutFail, CutCall] (CutListT m) x -> CutListT m x
cutListAlg oalg op
  | Just (Alg Empty)           <- prj op = empty
  | Just (Scp (Choose xs ys))  <- prj op = xs <|> ys
  | Just (Alg CutFail)         <- prj op = CutListT (\cons nil zero -> zero)
  | Just (Scp (CutCall xs))    <- prj op = CutListT (\cons nil zero -> runCutListT xs cons nil nil)

cutListAT :: AlgTrans [Empty, Choose, CutFail, CutCall] '[] '[CutListT] Monad
cutListAT = AlgTrans cutListAlg

cutList :: Handler [Empty, Choose, CutFail, CutCall] '[] '[CutListT] '[[]]
cutList = handler' fromCutListT cutListAlg

instance HFunctor CutListT where
  hmap :: (Functor f, Functor g) =>
    (forall x. f x -> g x) -> CutListT f a -> CutListT g a
  -- hmap h (CutListT xs) = CutListT (fmap (hmap h) (h x))
  hmap h (CutListT xs) = CutListT (undefined)

onceCut :: Handler '[Once] '[CutCall, CutFail, Choose] '[] '[]
onceCut = interpretM onceCutAlg

onceCutAT :: AlgTrans '[Once] '[CutCall, CutFail, Choose] '[] Monad
onceCutAT = AlgTrans onceCutAlg

onceCutAlg :: forall oeff m . 
     (Monad m , HFunctor (Effs oeff), Members [CutCall, CutFail, Choose] oeff)
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs '[Once] m x -> m x)
onceCutAlg oalg op
  | Just (Scp (Once p)) <- prj op
  = cutCallM oalg (do x <- p
                      eval oalg (do cut
                                    return x))

onceNondet :: Handler '[Once, Empty, Choose, CutFail, CutCall] '[] '[CutListT] '[[]]
onceNondet = onceCut |> cutList
