module Control.Monad.Trans.List where

import Control.Monad.Trans.Class ( MonadTrans(..) )
import Control.Applicative ( Alternative(empty, (<|>)) )
import Data.HFunctor ( HFunctor(..) )
import Control.Arrow ( Arrow(second) )
import Control.Monad ( ap, liftM, MonadPlus(..) )

newtype ListT m a = ListT { runListT :: m (Maybe (a, ListT m a)) }
  deriving Functor

runListT' :: Monad m => ListT m a -> m [a]
runListT' (ListT mmxs) =
  do mxs <- mmxs
     case mxs of
       Nothing         -> return []
       Just (x, mmxs') -> (x :) <$> runListT' mmxs'

instance HFunctor ListT where
  hmap :: (Functor f, Functor g) => (forall x1. f x1 -> g x1) -> ListT f x -> ListT g x
  hmap h (ListT mx) = ListT (fmap (fmap (fmap (hmap h))) (h mx))

foldListT :: Monad m => (a -> m b -> m b) -> m b -> ListT m a -> m b
foldListT k ys (ListT mxs) = mxs >>= maybe ys (\(x,xs) -> k x (foldListT k ys xs))

instance Monad m => Applicative (ListT m) where
  pure x = ListT (pure (Just (x, empty)))
  (<*>) = ap

instance Monad m => Monad (ListT m) where
  (>>=) :: Monad m => ListT m a -> (a -> ListT m b) -> ListT m b
  m >>= f = ListT $ foldListT (\x l -> runListT $ f x <|> ListT l) (return Nothing) m

instance Monad m => Alternative (ListT m) where
  empty = ListT (return Nothing)
  (<|>) :: Monad m => ListT m a -> ListT m a -> ListT m a
  ListT mxs <|> ListT mys = ListT $
    mxs >>= maybe mys (return . Just . second (<|> ListT mys))

instance Monad m => MonadPlus (ListT m) where
instance MonadTrans ListT where
  lift :: Monad m => m a -> ListT m a
  lift = ListT . liftM (\x -> Just (x, empty))
