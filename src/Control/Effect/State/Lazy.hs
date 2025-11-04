{-|
Module      : Control.Effect.State.Lazy
Description : Effects for the lazy state monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE LambdaCase #-}

module Control.Effect.State.Lazy
  ( -- * Syntax
    -- ** Operations
    put,
    get,

    -- ** Signatures
    Put, Put_ (..), pattern Put,
    Get, Get_ (..), pattern Get,

    -- * Semantics
    -- ** Handlers
    state, state_,

    -- ** Algebras
    stateAT,

    -- ** Re-export the carrier
    Lazy.StateT(..),
  ) where

import Control.Effect
import Control.Effect.State.Type
import Control.Effect.Family.Algebraic

import qualified Control.Monad.Trans.State.Lazy as Lazy

-- | The `state` handler deals with stateful operations and
-- returns the final state @s@.
state :: s -> Handler [Put s, Get s] '[] '[Lazy.StateT s] a (s, a)
state s = Handler (stateRun s) stateAT

-- | The `state_` handler deals with stateful operations and silenty
-- discards the final state.
state_ :: s -> Handler [Put s, Get s] '[] '[Lazy.StateT s] a a
state_ s = Handler (runner' $ flip Lazy.evalStateT s) stateAT

-- | An algebra transformer that interprets t'Get' and t'Put' using the lazy t'Lazy.StateT'.
stateAT :: AlgTrans [Put s, Get s] '[] '[Lazy.StateT s] Monad
stateAT = algTrans' $ \case
  Put s p -> do Lazy.put s; return p
  Get   p -> do s <- Lazy.get; return (p s)

stateRun :: s -> Runner '[] '[Lazy.StateT s] a (s, a) Monad
stateRun s = runner' $ fmap (\ ~(x, y) -> (y, x)) . flip Lazy.runStateT s
