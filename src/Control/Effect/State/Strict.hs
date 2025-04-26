{-|
Module      : Control.Effect.State.Strict
Description : Effects for the strict state monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}

module Control.Effect.State.Strict
  ( -- * Syntax
    -- ** Operations
    put
  , get

    -- ** Signatures
  , Put, Put_ (..)
  , Get, Get_ (..)

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
state :: s -> Handler [Put s, Get s] '[] '[Strict.StateT s] '[(,) s]
state s = handler' (fmap swap . flip Strict.runStateT s) stateAlg

-- | The `state_` handler deals with stateful operations and silenty
-- discards the final state.
{-# INLINE state_ #-}
state_ :: s -> Handler [Put s, Get s] '[] '[Strict.StateT s] '[]
state_ s = handler' (flip Strict.evalStateT s) stateAlg

-- | An algebra transformer that interprets t'Get' and t'Put' using the strict t'Strict.StateT'.
stateAT :: AlgTransM [Put s, Get s] '[] '[Strict.StateT s]
stateAT = AlgTrans stateAlg

-- | The underlying algebra of the state handler.
{-# INLINE stateAlg #-}
stateAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put s, Get s] (Strict.StateT s m) x -> Strict.StateT s m x)
stateAlg _ op
  | Just (Alg (Put s p)) <- prj op =
      do Strict.put s
         return p
  | Just (Alg (Get p)) <- prj op =
      do s <- Strict.get
         return (p s)