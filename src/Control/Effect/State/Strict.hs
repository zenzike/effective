{-|
Module      : Control.Effect.State.Strict
Description : Effects for the strict state monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE LambdaCase #-}

module Control.Effect.State.Strict
  ( -- * Syntax
    -- ** Operations
    put
  , get

    -- ** Signatures
  , Put, Put_ (..), pattern Put
  , Get, Get_ (..), pattern Get

    -- * Semantics
    -- ** Handlers
  , state, state_

    -- ** Algebras
  , stateAT

    -- ** Re-export the carrier
  , Strict.StateT(..),
  ) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.State.Type

import qualified Control.Monad.Trans.State.Strict as Strict
import Data.Tuple (swap)

-- | The `state` handler deals with stateful operations and
-- returns the final state @s@.
{-# INLINE state #-}
state :: s -> Handler [Put s, Get s] '[] '[Strict.StateT s] a (s, a)
state s = Handler (runner' $ fmap swap . flip Strict.runStateT s) stateAT

-- | The `state_` handler deals with stateful operations and silenty
-- discards the final state.
{-# INLINE state_ #-}
state_ :: s -> Handler [Put s, Get s] '[] '[Strict.StateT s] a a
state_ s = Handler (runner' $ flip Strict.evalStateT s) stateAT

-- | An algebra transformer that interprets t'Get' and t'Put' using the strict t'Strict.StateT'.
{-# INLINE stateAT #-}
stateAT :: AlgTrans [Put s, Get s] '[] '[Strict.StateT s] Monad
stateAT = algTrans' $ \case
  Put s p -> do Strict.put s; return p
  Get   p -> do s <- Strict.get; return (p s)