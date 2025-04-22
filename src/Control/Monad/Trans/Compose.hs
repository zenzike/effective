{-|
Module      : Control.Monad.Trans.Compose
Description : Higher-order functor composition
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
#if __GLASGOW_HASKELL__ <= 904
{-# LANGUAGE QuantifiedConstraints #-}
#endif
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.Monad.Trans.Compose where

import Control.Applicative
import Control.Monad.Trans.Class
import Data.Kind (Type)
import Data.Coerce

-- | Right-to-left composition of higher-order functors. A higher-order version
-- of 'Data.Functor.Compose'.
newtype ComposeT (h :: (Type -> Type) -> (Type -> Type))
                 (k :: (Type -> Type) -> (Type -> Type))
                 (f :: (Type -> Type)) (a :: Type)
  = ComposeT { getComposeT :: h (k f) a }

instance (Applicative m, Alternative (t1 (t2 m))) => Alternative (ComposeT t1 t2 m) where
  empty :: forall a . ComposeT t1 t2 m a
  empty = coerce (empty :: t1 (t2 m) a)

  (<|>) :: forall a . ComposeT t1 t2 m a -> ComposeT t1 t2 m a -> ComposeT t1 t2 m a
  (<|>) = coerce ((<|>) :: t1 (t2 m) a -> t1 (t2 m) a -> t1 (t2 m) a)

  many :: forall a . ComposeT t1 t2 m a -> ComposeT t1 t2 m [a]
  many = coerce (many :: t1 (t2 m) a -> t1 (t2 m) [a])

  some :: forall a . ComposeT t1 t2 m a -> ComposeT t1 t2 m [a]
  some = coerce (some :: t1 (t2 m) a -> t1 (t2 m) [a])

instance Functor (h (k m)) => Functor (ComposeT h k m) where
    {-# INLINE fmap #-}
    fmap :: forall a b . (a -> b) -> ComposeT h k m a -> ComposeT h k m b
    fmap = coerce (fmap :: (a -> b) -> h (k m) a -> h (k m) b)

instance (Applicative (h (k f))) =>
  Applicative (ComposeT h k f) where

    {-# INLINE pure #-}
    pure :: forall a . a -> ComposeT h k f a
    pure = coerce (pure :: a -> h (k f) a)

    {-# INLINE (<*>) #-}
    (<*>) :: forall a b . ComposeT h k f (a -> b) -> ComposeT h k f a -> ComposeT h k f b
    (<*>) = coerce ((<*>) :: h (k f) (a -> b) -> h (k f) a -> h (k f) b)

    {-# INLINE (<*) #-}
    (<*) :: forall a b . ComposeT h k f a -> ComposeT h k f b -> ComposeT h k f a
    (<*) = coerce ((<*) :: h (k f) a -> h (k f) b -> h (k f) a)

    {-# INLINE (*>) #-}
    (*>) :: forall a b . ComposeT h k f a -> ComposeT h k f b -> ComposeT h k f b
    (*>) = coerce ((*>) :: h (k f) a -> h (k f) b -> h (k f) b)

    {-# INLINE liftA2 #-}
    liftA2 :: forall a b c . (a -> b -> c) -> ComposeT h k f a -> ComposeT h k f b -> ComposeT h k f c
    liftA2 = coerce (liftA2 :: (a -> b -> c) -> h (k f) a -> h (k f) b -> h (k f) c)

instance (Monad (t1 (t2 m))) => Monad (ComposeT t1 t2 m) where
    {-# INLINE return #-}
    return :: forall a . a -> ComposeT t1 t2 m a
    return = coerce (return :: a -> t1 (t2 m) a)

    {-# INLINE (>>=) #-}
    (>>=) :: forall a b . ComposeT t1 t2 m a -> (a -> ComposeT t1 t2 m b) -> ComposeT t1 t2 m b
    (>>=) = coerce ((>>=) :: t1 (t2 m) a -> (a -> t1 (t2 m) b) -> t1 (t2 m) b)

    {-# INLINE (>>) #-}
    (>>) :: forall a b . ComposeT t1 t2 m a -> ComposeT t1 t2 m b -> ComposeT t1 t2 m b
    (>>) = coerce ((>>) :: t1 (t2 m) a -> t1 (t2 m) b -> t1 (t2 m) b)

#if __GLASGOW_HASKELL__ <= 904
instance (MonadTrans t1, MonadTrans t2, forall m . Monad m => Monad (t2 m)) =>
#else
instance (MonadTrans t1, MonadTrans t2) =>
#endif
  MonadTrans (ComposeT t1 t2) where
    {-# INLINE lift #-}
    lift :: Monad m => m a -> ComposeT t1 t2 m a
    lift x = ComposeT (lift (lift x))
