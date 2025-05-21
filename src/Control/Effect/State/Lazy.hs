{-|
Module      : Control.Effect.State.Lazy
Description : Effects for the lazy state monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}

module Control.Effect.State.Lazy
  ( -- * Syntax
    -- ** Operations
    put,
    get,

    -- ** Signatures
    Put, Put_ (..),
    Get, Get_ (..),

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
state :: s -> Handler [Put s, Get s] '[] '[Lazy.StateT s] '[(,) s]
state s = handler' (fmap (\ ~(x, y) -> (y, x)) . flip Lazy.runStateT s) stateAlg

-- | The `state_` handler deals with stateful operations and silenty
-- discards the final state.
state_ :: s -> Handler [Put s, Get s] '[] '[Lazy.StateT s] '[]
state_ s = handler' (flip Lazy.evalStateT s) stateAlg

-- | An algebra transformer that interprets t'Get' and t'Put' using the lazy t'Lazy.StateT'.
stateAT :: AlgTrans [Put s, Get s] '[] '[Lazy.StateT s] Monad
stateAT = AlgTrans stateAlg

-- | The underlying algebra of the state handler.
stateAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put s, Get s] (Lazy.StateT s m) x -> Lazy.StateT s m x)
stateAlg _ op
  | Just (Alg (Put s p)) <- prj op =
      do Lazy.put s
         return p
  | Just (Alg (Get p)) <- prj op =
      do s <- Lazy.get
         return (p s)