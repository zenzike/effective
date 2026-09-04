{-|
Module      : Control.Effect.State
Description : Effects for the state monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides access to stateful operations and handlers.
The implementation uses strict state by default, offered by "Control.Effect.State.Strict".
For lazy state, import "Control.Effect.State.Lazy" instead.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.State
  ( module Control.Effect.State.Operations,
    module Control.Effect.State.Strict
  ) where

import Control.Effect.State.Operations
import Control.Effect.State.Strict