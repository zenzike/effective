module Control.Monad.Trans.Resump (
  ResT(..),
  foldRes,
  resOp, resOp',
) where

import Data.HFunctor ( HFunctor(..) )

import Control.Monad
import Data.Bifunctor ( Bifunctor(bimap) )
import Control.Monad.Trans.Class ( MonadTrans(..) )


newtype ResT s m a = ResT { unResT :: m (Either a (s (ResT s m a))) }

instance (Functor s, Functor m) => Functor (ResT s m) where
  fmap f (ResT m) = ResT $ fmap (bimap f (fmap (fmap f))) m

instance (Functor s, Monad m) => Applicative (ResT s m) where
  {-# INLINE pure #-}
  pure x = ResT (return (Left x))

  {-# INLINE (<*>) #-}
  (<*>) = ap

instance (Functor s, Monad m) => Monad (ResT s m) where
  ResT r >>= k = ResT $
     do x <- r
        case x of
          Left x   -> unResT (k x)
          Right sr -> return (Right (fmap (>>= k) sr))

instance (Functor s) => HFunctor (ResT s) where
  {-# INLINE hmap #-}
  hmap h (ResT mx) = ResT (fmap (fmap (fmap (hmap h))) (h mx))

instance (Functor s) => MonadTrans (ResT s) where
  lift m = ResT (fmap Left m)

resOp :: Monad m => s (ResT s m a) -> ResT s m a
resOp o = ResT $ return (Right o)

resOp' :: (Functor s, Monad m) => s a -> ResT s m a
resOp' o = ResT $ return (Right (fmap return o))

foldRes :: (Functor s, Monad m) => (a -> m t) -> (s (m t) -> m t) -> ResT s m a -> m t
foldRes ret salg r = 
  do e <- unResT r
     case e of
       Left  x -> ret x
       Right s -> salg (fmap (foldRes ret salg) s)