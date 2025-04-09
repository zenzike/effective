{-|
Module      : Control.Effect
Description : Main module for the effective library
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module contains the core types and functions for working with effects.
The README file contains a tutorial on how to use this library.
-}

module Control.Effect
  ( -- * Programs
    Progs
  , Prog
  , Effs (Eff, Effs)
  , call
  , callM
  , call'
  , callM'
  , weakenProg
  , Effect

  -- * Operations
  , Member(..)
  , Members(..)
  , prj
  , inj
  , Injects( injs )
  , Append (..)

  -- * Algebras
  , Algebra
  , (#)
  , Forward (..)
  , Forwards (..)
  , absurdEffs

  -- * Handlers
  , Handler (..)
  , handler
  , interpret
  , interpretM
  , identity
  , fuse, (|>)
  , pipe, (||>)
  , hide

  -- * Evaluation
  , eval
  , fold
  , handle
  , handleM

  -- * Type families
  -- | The types of handlers are normalised when they are fused together, as are
  -- any results when a handler is applied. This normalisation removes unnecessary
  -- t`Identity`, t`Compose`, t`IdentityT`, and t`ComposeT` functors.
  , Apply
  , HApply
  , RAssoc
  , HRAssoc

  -- * Re-exports
  , Compose(..)
  , Identity(..)
  , ComposeT(..)
  , IdentityT(..)
  ) where

import Data.Functor.Identity
import Data.Functor.Compose
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Compose

import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Handler
import Control.Effect.Internal.Forward
