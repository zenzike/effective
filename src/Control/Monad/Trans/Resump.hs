module Control.Monad.Trans.Resump where

import Data.HFunctor ( HFunctor(..) )

import Control.Monad
import Data.Bifunctor ( Bifunctor(bimap) )
import Control.Monad.Trans.Class ( MonadTrans(..) )

type f :+: g = Either f g

newtype ResT s m a = ResT { unResT :: m (a :+: s (ResT s m a)) }

instance (Functor s, Functor m) => Functor (ResT s m) where
  fmap f (ResT m) = ResT $ fmap (bimap f (fmap (fmap f))) m

instance (Functor s, Monad m) => Applicative (ResT s m) where
  {-# INLINE pure #-}
  pure x = ResT (return (Left x))

  {-# INLINE (<*>) #-}
  (<*>) = ap

instance (Functor s, Monad m) => Monad (ResT s m) where
  (ResT r) >>= k = ResT $
     do x <- r
        case x of
          Left x   -> unResT (k x)
          Right sr -> return (Right (fmap (>>= k) sr))

instance (Functor s) => HFunctor (ResT s) where
  {-# INLINE hmap #-}
  hmap h (ResT mx) = ResT (fmap (fmap (fmap (hmap h))) (h mx))

instance MonadTrans (ResT s) where
  lift m = ResT (fmap Left m)
