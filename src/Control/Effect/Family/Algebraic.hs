{-|
Module      : Control.Effect.Algebraic
Description : The algebraic effect family
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module defines The family of algebraic operations. For every functor 
@sig :: Type -> Type@, an algebraic operation of signature @sig@ on a monad
@m@ is a function @op :: forall a. sig (m a) -> m a@ satisfying the following
property:

> op x >>= k  ==  op (fmap (>>= k) x)

for all @x :: sig (m a)@ and @k :: a -> m b@. Such operations are in bijection
with polymorphic functions of type @forall a. sig a -> m a@, witnessed by
`algOpIso` below.

An important property of algebraic operations is that they can always be
lifted through any monad transformer in a canonical way.  This is witnessed by
the @Forward@ instance.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Family.Algebraic where

import Control.Effect

import Data.Iso
import Data.Kind ( Type )
import Data.HFunctor
import Control.Monad.Trans.Class

-- | @Alg sig@ is the (higher-order) signature of algebraic operations of 
-- (first-order) signature @sig@.

newtype Alg (sig :: Type -> Type)
         (f :: Type -> Type)
         k
         = Alg (sig k)

instance Functor sig => Functor (Alg sig f) where
  {-# INLINE fmap #-}
  fmap f (Alg op) = Alg (fmap f op)

instance Functor sig => HFunctor (Alg sig) where
  {-# INLINE hmap #-}
  hmap f (Alg op) = Alg op

-- | Algebraic operations can be lifted along any monad transformers canonically.
-- We mark this instance as incoherent because for specific monad transformers we may
-- have more general lifting instances. For example, we trivially have
--
-- > instance Forward eff IdentityT
--
-- And this is not strictly more speicific than @Forward (Alg f) t@ so we need the
-- instance here to be incoherent.
instance {-# INCOHERENT #-} MonadTrans t => Forward (Alg f) t where
  {-# INLINE fwd #-}
  fwd alg (Alg op) = lift (alg (Alg op))

-- | Functions @forall x. Alg sig m x -> m x@ are the same as @forall x. sig x -> m x@,
-- and they are in bijection with functions @op :: forall x. sig (m x) -> m x@ satisfying
-- the equation @op x >>= k  ==  op (fmap (>>= k) x)@.
algOpIso :: (Functor sig, Monad m) 
         => Iso (forall x. Alg sig m x -> m x) (forall x. sig (m x) -> m x) 
algOpIso = Iso 
  (\a sm -> a (Alg sm) >>= id)
  (\b (Alg s) -> b (fmap return s))