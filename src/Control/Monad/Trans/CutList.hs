{-|
Module      : Control.Monad.Trans.CutList
Description : CutList monad transformer
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

module Control.Monad.Trans.CutList where

import Control.Applicative
import Control.Monad.Trans.Class

-- | The t`CutListT` transformer builds a cut list, which is similar to a
-- list but includes a @cut@ operation from logic programming.
-- The Church encoding is used for efficiency.
newtype CutListT m a = CutListT
  { runCutListT :: forall b . (a -> m b -> m b) -> m b -> m b -> m b }
  deriving Functor

instance Monad m => Applicative (CutListT m) where
  pure x = CutListT (\cons nil zero -> cons x nil)

  CutListT fs <*> CutListT xs = CutListT $ \cons nil zero ->
    fs (\f fs' -> xs (cons . f) fs' zero) nil zero

instance Monad m => Alternative (CutListT m) where
  empty = CutListT (\cons nil zero -> nil)

  CutListT xs <|> CutListT ys = CutListT $ \cons nil zero ->
    xs cons (ys cons nil zero) zero

instance Monad m => Monad (CutListT m) where
  CutListT xs >>= k = CutListT $ \cons nil zero ->
    xs (\x xs' -> runCutListT (k x) cons xs' zero) nil zero

instance MonadTrans CutListT where
  lift :: Monad m => m a -> CutListT m a
  lift mx = CutListT $ \cons nil zero ->
    mx >>= flip cons nil

-- | Extracts an alternative from a t`CutListT` in the context @m@.
fromCutListT :: (Alternative f, Monad m) => CutListT m a -> m (f a)
fromCutListT (CutListT xs) =
  xs (fmap . (<|>) . pure) (pure empty) (pure empty)