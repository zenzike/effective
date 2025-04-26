{-|
Module      : Control.Effect.Alternative
Description : Effects for alternatives with choose and empty
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Effect.Alternative (
  -- * Syntax
  -- ** Operations

  -- | The operations for alternatives use 'empty' and '<|>' directly
  -- from the 'Control.Applicative.Alternative' type class.
  --
  -- 'empty' is an algebraic operation:
  --
  -- > empty >>= k = empty
  --
  -- '<|>' is a scoped operation.
  empty,

  (<|>),

  -- ** Signatures
  Empty, Empty_(..),
  Choose, Choose_(..),

  -- * Semantics
  -- ** Handlers
  alternative,

  -- ** Algebras
  alternativeAT,
) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Applicative ( Alternative(empty, (<|>)) )

-- | Signature for empty alternatives.
type Empty = Alg Empty_
-- | Underlying signature for empty alternatives.
data Empty_ a where
  Empty :: Empty_ a
  deriving Functor

-- | Signature for choice of alternatives.
type Choose = Scp Choose_
-- | Underlying signature for choice of alternatives.
data Choose_ a where
  Choose :: a -> a -> Choose_ a
  deriving Functor

-- | The 'alternative' handler makes use of an 'Alternative' functor @f@
-- as well as a transformer @t@ that produces an 'Alternative' functor @t m@.
-- for any monad @m@ to provide semantics.
alternative
  :: forall t f
  .  (forall m . Monad m => Alternative (t m))
  => (forall m . Monad m => (forall a . t m a -> m (f a)))
  -> Handler '[Empty, Choose] '[] '[t] '[f]
alternative run = handler' run alternativeAlg

-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying 'Alternative' instance for @t m@ given by a transformer @t@.
alternativeAT
  :: forall t. (forall m . Monad m => Alternative (t m))
  => AlgTransM '[Empty, Choose] '[] '[t]
alternativeAT = AlgTrans alternativeAlg

alternativeAlg
  :: forall oeffs t . (forall m . Monad m => Alternative (t m))
  => forall m. Monad m 
  => Algebra oeffs m -> Algebra [Empty, Choose] (t m)
alternativeAlg oalg eff
  | (Just (Alg Empty))          <- prj eff = empty
  | (Just (Scp (Choose xs ys))) <- prj eff = xs <|> ys

-- | Instance for 'Alternative' that uses 'Choose_ and 'Empty_.
instance (Member Choose sigs, Member Empty sigs)
  => Alternative (Prog sigs) where
  {-# INLINE empty #-}
-- | Syntax for an empty alternative. This is an algebraic operation.
  empty = call (Alg Empty)

  {-# INLINE (<|>) #-}
-- | Syntax for a choice of alternatives. This is a scoped operation.
  xs <|> ys = call (Scp (Choose (fmap return xs) (fmap return ys)))
