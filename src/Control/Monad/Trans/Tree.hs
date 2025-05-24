{-|
Module      : Control.Monad.Trans.YRes
Description : Resumption monad transformer for yield-based coroutine
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains a special case of the resumption monad from "Control.Monad.Trans.CRes"
with the step functor being @x ↦  a × (b -> x)@ for types @a@ and @b@. This
is used for modelling yield-based coroutines.
-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- Tree transformer implementation from `NonDetC` in `fused-effects`
module Control.Monad.Trans.Tree
( runTreeT
, runTreeA
, runTreeM
, TreeT(..)
) where

import Control.Applicative
import Control.Monad.Trans.Class

newtype TreeT m a = TreeT (forall b . (m b -> m b -> m b) -> (a -> m b) -> m b -> m b)
  deriving Functor

runTreeT
  :: (m b -> m b -> m b)
  -> (a -> m b)
  -> m b
  -> TreeT m a
  -> m b
runTreeT fork leaf nil (TreeT m) = m fork leaf nil
{-# INLINE runTreeT #-}

runTreeA :: (Alternative f, Applicative m) => TreeT m a -> m (f a)
runTreeA = runTreeT (liftA2 (<|>)) (pure . pure) (pure empty)
{-# INLINE runTreeA #-}

runTreeM :: (Applicative m, Monoid b) => (a -> b) -> TreeT m a -> m b
runTreeM leaf = runTreeT (liftA2 mappend) (pure . leaf) (pure mempty)
{-# INLINE runTreeM #-}

instance Applicative (TreeT m) where
  pure a = TreeT (\ _ leaf _ -> leaf a)
  {-# INLINE pure #-}

  TreeT f <*> TreeT a = TreeT $ \ fork leaf nil ->
    f fork (\ f' -> a fork (leaf . f') nil) nil
  {-# INLINE (<*>) #-}

instance Alternative (TreeT m) where
  empty = TreeT (\ _ _ nil -> nil)
  {-# INLINE empty #-}

  TreeT l <|> TreeT r = TreeT $ \ fork leaf nil ->
    l fork leaf nil `fork` r fork leaf nil
  {-# INLINE (<|>) #-}

instance Monad (TreeT m) where
  TreeT a >>= f = TreeT $ \ fork leaf nil ->
    a fork (runTreeT fork leaf nil . f) nil
  {-# INLINE (>>=) #-}

instance MonadTrans TreeT where
  lift m = TreeT (\ _ leaf _ -> m >>= leaf)
  {-# INLINE lift #-}
