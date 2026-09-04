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
    module Control.Effect.State.Operations

    -- * Semantics
    -- ** Handlers
  , state, state_
  , stateC, stateC_

    -- ** Algebras
  , stateAT

    -- ** Re-export the carrier
  , Strict.StateT(..),
  ) where

import Control.Effect
import Control.Effect.State.Operations
import Data.Tuple (swap)

import qualified Control.Monad.Trans.State.Strict as Strict

{-# INLINE putAlg #-}
putAlg :: Monad m => Put s f b -> Strict.StateT s m b
putAlg (Put s p) = do Strict.put s; return p

{-# INLINE getAlg #-}
getAlg :: Monad m => Get s f b -> Strict.StateT s m b
getAlg (Get p) = do s <- Strict.get; return (p s)

-- | An algebra transformer that interprets t'Get' and t'Put' using the strict t'Strict.StateT'.
{-# INLINE stateAT #-}
stateAT :: AlgTrans [Put s, Get s] '[] '[Strict.StateT s] Monad
stateAT = algTrans' $ putAlg :#. getAlg

stateATC :: AlgTransC [Put s, Get s] '[] '[Strict.StateT s] Monad
stateATC = AlgTransC $ \_ -> [|| NT $ putAlg ||] :#$ [|| NT $ getAlg ||] :#$ emptyAlgC

-- | The `state` handler deals with stateful operations and
-- returns the result and final state @s@.
{-# INLINE state #-}
state :: s -> Handler [Put s, Get s] '[] '[Strict.StateT s] a (a, s)
state s = Handler (runner' $ flip Strict.runStateT s) stateAT

-- | The `state_` handler deals with stateful operations and silently
-- discards the final state.
{-# INLINE state_ #-}
state_ :: s -> Handler [Put s, Get s] '[] '[Strict.StateT s] a a
state_ s = Handler (runner' $ flip Strict.evalStateT s) stateAT

-- Handlers for lightweight staging

stateC :: CodeQ s -> HandlerC [Put s, Get s] '[] '[Strict.StateT s] a (a, s)
stateC cs = HandlerC
  (RunnerC $ \_ -> [|| flip Strict.runStateT $$cs ||])
  (AlgTransC $ \_ -> [|| NT $ putAlg ||] :#$ [|| NT $ getAlg ||] :#$ emptyAlgC)

stateC_ :: CodeQ s -> HandlerC [Put s, Get s] '[] '[Strict.StateT s] a a
stateC_ cs = HandlerC
  (RunnerC $ \_ -> [|| flip Strict.evalStateT $$cs ||])
  (AlgTransC $ \_ -> [|| NT $ putAlg ||] :#$ [|| NT $ getAlg ||] :#$ emptyAlgC)
