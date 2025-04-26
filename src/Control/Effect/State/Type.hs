{-|
Module      : Control.Effect.State.Type
Description : Types for state effect
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}

module Control.Effect.State.Type where

import Control.Effect
import Control.Effect.Family.Algebraic

-- | Signature for putting a value into the state.
type Put s = Alg (Put_ s)
-- | Underlying signature for putting a value into the state.
data Put_ s k where
  Put :: s -> k -> Put_ s k
  deriving Functor

-- | Syntax for putting a value into the state.
{-# INLINE put #-}
put :: Member (Put s) sig => s -> Prog sig ()
put s = call (Alg (Put s (return ())))

-- | Signature for getting a value from the state.
type Get s = Alg (Get_ s)

-- | Underlying signature for getting a value from the state.
newtype Get_ s k where
  Get :: (s -> k) -> Get_ s k
  deriving Functor

-- | Syntax for getting a value from the state.
{-# INLINE get #-}
get :: Member (Get s) sig => Prog sig s
get = call (Alg (Get return))
