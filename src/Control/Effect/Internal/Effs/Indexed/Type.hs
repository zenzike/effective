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

module Control.Effect.Internal.Effs.Indexed.Type where

import Data.Kind ( Type )
import Data.List.Kind

import GHC.TypeLits
import GHC.Exts

-- | The type of higher-order effects.
type Effect = (Type -> Type) -> (Type -> Type)

-- | A higher-order algebra for the union of effects @effs@ with
-- carrier being the functor @f@.
type Algebra effs f =
  forall x . Effs effs f x -> f x

-- | @Effs effs f a@ creates a union of the effect signatures in the list @effs@.
type Effs :: [Effect] -> Effect
data Effs effs f a where
  -- | @`Effn` n op@ places an operation @n@ away from the last element of the list.
  Effn :: {-# UNPACK #-} !Int -> !(eff f a) -> Effs effs f a

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

-- | @Member eff effs@ holds when @eff@ is contained in @effs@.
type Member :: Effect -> [Effect] -> Constraint
type Member eff effs = (KnownNat (EffIndex eff effs))

-- | @Member effs effs'@ holds when every @eff@ which is a 'Member' of in @effs@
-- is also a 'Member' of @effs'@.
type family Members (xeffs :: [Effect]) (xyeffs :: [Effect]) :: Constraint where
  Members '[] xyeffs       = ()
  Members (xeff ': xeffs) xyeffs = (Member xeff xyeffs, Members xeffs xyeffs)
