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
  , ProgAlg(..)
  , ProgX
  , ProgZ
  , acall
  , Effs (Eff, Effs)
  , call
  , weakenProg
  , Effect
  , Reifies

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

  , MAlgebra (..)
  , MAlgebraZ (..)
  , Syntax
  , mcall
  , xcall
  , zcall

  , Forward (..)
  , Forwards (..)
  , absurdEffs

  -- * Handlers
  , Handler (..)
  , handler
  , handles
  , handleX
  , handleZ
  , handleA
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
  , handleN
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
import Control.Effect.Internal.MAlgebra
