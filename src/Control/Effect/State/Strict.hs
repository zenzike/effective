{-|
Module      : Control.Effect.State.Strict
Description : Effects for the strict state monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.State.Strict
  ( -- * Syntax
    -- ** Operations
    put
  , get
  , put'
  , get'
  , putX
  , getX
  , getZ
  , putZ
  , getA
  , putA

    -- ** Signatures
  , Put, Put_ (..)
  , Get, Get_ (..)

    -- * Semantics
    -- ** Handlers
  , state, state_

    -- ** Algebras
  , stateAlg
  ) where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.State.Type

import qualified Control.Monad.Trans.State.Strict as Strict
import Data.Tuple (swap)

{-# INLINE state #-}
-- | The `state` handler deals with stateful operations and
-- returns the final state @s@.
state :: s -> Handler [Put s, Get s] '[] (Strict.StateT s) ((,) s)
state s = handler (fmap swap . flip Strict.runStateT s) stateAlg

{-# INLINE state_ #-}
-- | The `state_` handler deals with stateful operations and silenty
-- discards the final state.
state_ :: s -> Handler [Put s, Get s] '[] (Strict.StateT s) Identity
state_ s = handler (fmap Identity . flip Strict.evalStateT s) stateAlg

-- runState_ :: Monad m => s -> Algebra '[] m -> (forall x.  Strict.StateT s m x -> m (Identity x))
-- runState_ s = fmap Identity . flip Strict.evalStateT s

-- | An algebra that interprets t'Get' and t'Put' using the strict t'Strict.StateT'.
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

instance MAlgebra (Strict.StateT s) where
  type IEffs (Strict.StateT s) = '[Put s, Get s]
  type OEffs (Strict.StateT s) = '[]

  {-# INLINE malg #-}
  malg = stateAlg
