module Control.Monad.Trans.List where

import Data.HFunctor ( HFunctor(..) )

import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad
import Control.Monad.Trans.Class ( MonadTrans(..) )

newtype ListT m a = ListT { runListT :: m (Maybe (a, ListT m a)) }
  deriving Functor

{-# INLINE runListT' #-}
runListT' :: Monad m => ListT m a -> m [a]
runListT' (ListT mmxs) =
  do mxs <- mmxs
     case mxs of
       Nothing         -> return []
       Just (x, mmxs') -> (x :) <$> runListT' mmxs'

instance HFunctor ListT where
  {-# INLINE hmap #-}
  hmap :: (Functor f, Functor g) => (forall x1. f x1 -> g x1) -> ListT f x -> ListT g x
  hmap h (ListT mx) = ListT (fmap (fmap (fmap (hmap h))) (h mx))

{-# INLINE foldListT #-}
foldListT :: Monad m => (a -> m b -> m b) -> m b -> ListT m a -> m b
foldListT f k tmxs = go tmxs where
  go (ListT mxs) = mxs >>= maybe k (\(x,xs) -> f x (go xs))

{-
-- The above is a static argument transformed version of this:
foldListT :: Monad m => (a -> m b -> m b) -> m b -> ListT m a -> m b
foldListT k ys (ListT mxs) = mxs >>= maybe ys (\(x,xs) -> k x (foldListT k ys xs))
-}

instance Monad m => Applicative (ListT m) where
  {-# INLINE pure #-}
  pure x = ListT (pure (Just (x, empty)))

  {-# INLINE (<*>) #-}
  (<*>) = ap

instance Monad m => Monad (ListT m) where
  {-# INLINE (>>=) #-}
  (>>=) :: Monad m => ListT m a -> (a -> ListT m b) -> ListT m b
  m >>= f = ListT $ foldListT (\x l -> runListT $ f x <|> ListT l) (return Nothing) m

instance Monad m => Alternative (ListT m) where
  {-# INLINE empty #-}
  empty = ListT (return Nothing)
  {-# INLINE (<|>) #-}
  (<|>) :: Monad m => ListT m a -> ListT m a -> ListT m a
  mxs <|> ListT mys = ListT (foldListT f mys mxs) where
    f :: a -> (m (Maybe (a, ListT m a))) -> (m (Maybe (a, ListT m a)))
    f x xs = return (Just (x, ListT xs))

instance MonadTrans ListT where
  {-# INLINE lift #-}
  lift :: Monad m => m a -> ListT m a
  lift = ListT . liftM (\x -> Just (x, empty))

instance Monad m => MonadPlus (ListT m) where
  {-# INLINE mzero #-}
  mzero = empty
  {-# INLINE mplus #-}
  mplus = (<|>)