{-|
Module      : Control.Effect.Internal.Effs.Type
Description : The union type for effect operations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Internal.Effs.Sum.Type
  ( Effs (..)
  , Algebra
  , Effect
  , absurdEffs
  ) where

import Data.Kind ( Type )
import Data.HFunctor
import Data.List.Kind

import GHC.TypeLits

-- | The type of higher-order effects.
type Effect = (Type -> Type) -> (Type -> Type)

-- | A higher-order algebra for the union of effects @effs@ with
-- carrier being the functor @f@.
type Algebra effs f =
  forall x . Effs effs f x -> f x

-- | @Effs effs f a@ creates a union of the effect signatures in the list @effs@.
type Effs :: [Effect] -> Effect
data Effs sigs f a where
  Eff  :: !(sig f a) -> Effs (sig ': sigs) f a
  Effs :: !(Effs sigs f a) -> Effs (sig ': sigs) f a

instance Functor f => Functor (Effs '[] f) where
  {-# INLINE fmap #-}
  fmap f x = case x of {}

instance (Functor f, Functor (eff f), Functor (Effs effs f)) => Functor (Effs (eff ': effs) f) where
  {-# INLINE fmap #-}
  fmap f (Eff x)  = Eff (fmap f x)
  fmap f (Effs x) = Effs (fmap f x)

instance HFunctor (Effs '[]) where
  {-# INLINE hmap #-}
  hmap h x = case x of {}

instance (HFunctor (Effs effs), HFunctor eff) => HFunctor (Effs (eff ': effs)) where
  {-# INLINE hmap #-}
  hmap h (Eff x)  = Eff (hmap h x)
  hmap h (Effs x) = Effs (hmap h x)

-- | @`EffIndex` eff effs@ finds the index of @eff@ in @effs@, where
-- the last element has index @0@, and the head element has index @Length effs - 1@.
type family EffIndex (eff :: a) (effs :: [a]) :: Nat where
  EffIndex eff (eff ': effs) = Length effs
  EffIndex eff (_ ': effs)   = EffIndex eff effs

-- | Given @xeffs@ which is a subset of effects in @yeffs@, @`EffIndexes` xeffs
-- yeffs@ finds the index @`EffIndex` eff yeffs@ for each @eff@ in @xeffs@, and
-- returns this as a list of indices.
type family EffIndexes (xeffs :: [a]) (yeffs :: [a]) :: [Nat] where
  EffIndexes '[] yeffs            = '[]
  EffIndexes (eff ': xeffs) yeffs = EffIndex eff yeffs ': EffIndexes xeffs yeffs

-- | A value of type @Effs '[] f x@ cannot be created, and this is the
-- absurd destructor for this type.
{-# INLINE absurdEffs #-}
absurdEffs :: Effs '[] f x -> a
absurdEffs x = case x of {}