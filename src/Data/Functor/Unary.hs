{-|
Module      : Data.Functor.Unary
Description : Functors for unary effectful operations with parameters.
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental
-}

module Data.Functor.Unary where
import Data.Functor.Identity

-- | `Unary f` says that the functor `f` is the signature for a unary operation
-- possibly with some parameters.
class (Functor f) => Unary f where
  -- | Extracting the unique element @x@ stored in @f x@.
  get :: f x -> x

  -- | Modifying the unique element @x@ stored in @f x@.
  upd :: f x -> y -> f y
  upd fx y = fmap (const y) fx

instance Unary Identity where
  get = runIdentity

instance Unary ((,) a) where
  get = snd

instance Unary ((->) ()) where
  get fx = fx ()