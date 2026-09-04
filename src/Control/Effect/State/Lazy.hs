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
    module Control.Effect.State.Operations,

    -- * Semantics
    -- ** Handlers
    state, state_,
    stateC, stateC_,

    -- ** Algebras
    stateAT,

    -- ** Re-export the carrier
    Lazy.StateT(..),
  ) where

import Control.Effect
import Control.Effect.State.Operations
import Control.Effect.Family.Algebraic

import qualified Control.Monad.Trans.State.Lazy as Lazy

-- | The `state` handler deals with stateful operations and
-- returns the result and final state @s@.
state :: s -> Handler [Put s, Get s] '[] '[Lazy.StateT s] a (a, s)
state s = Handler (runner' $ flip Lazy.runStateT s) stateAT

-- | The `state_` handler deals with stateful operations and silently
-- discards the final state.
state_ :: s -> Handler [Put s, Get s] '[] '[Lazy.StateT s] a a
state_ s = Handler (runner' $ flip Lazy.evalStateT s) stateAT

-- | An algebra transformer that interprets t'Get' and t'Put' using the lazy t'Lazy.StateT'.
stateAT :: AlgTrans [Put s, Get s] '[] '[Lazy.StateT s] Monad
stateAT = algTrans' $ putAlg :#. getAlg

{-# INLINE putAlg #-}
putAlg :: Monad m => Put s f b -> Lazy.StateT s m b
putAlg (Put s p) = do Lazy.put s; return p

{-# INLINE getAlg #-}
getAlg :: Monad m => Get s f b -> Lazy.StateT s m b
getAlg (Get p) = do s <- Lazy.get; return (p s)

-- Handlers for lightweight staging

stateC :: CodeQ s -> HandlerC [Put s, Get s] '[] '[Lazy.StateT s] a (a, s)
stateC cs = HandlerC
  (RunnerC $ \_ -> [|| flip Lazy.runStateT $$cs ||])
  (AlgTransC $ \_ -> [|| NT $ putAlg ||] :#$ [|| NT $ getAlg ||] :#$ emptyAlgC)

stateC_ :: CodeQ s -> HandlerC [Put s, Get s] '[] '[Lazy.StateT s] a a
stateC_ cs = HandlerC
  (RunnerC $ \_ -> [|| flip Lazy.evalStateT $$cs ||])
  (AlgTransC $ \_ -> [|| NT $ putAlg ||] :#$ [|| NT $ getAlg ||] :#$ emptyAlgC)
