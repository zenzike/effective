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
  , callK
  , callM
  , call'
  , callM'
  , weakenProg
  , progAlg
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
  , singAlgIso
  , (#)
  , Forward (..)
  , Forwards (..)
  , absurdEffs

  -- * Handlers
  , Handler (..)
  , handler
  , handler'
  , interpret
  , interpret1
  , interpretM
  , identity
  , fuse, (|>)
  , pipe, (||>)
  , hide

  -- * Algebra transformers
  , AlgTrans (..)
  , AlgTransM 
  , asAT
  , idAT
  , compAT
  , weakenAT
  , fuseAT
  , pipeAT
  , passAT


  -- * Evaluation
  , eval
 -- , fold
  , handle
  , handleM
  , handleP
  , handleM'
  , handleP'
  , handleMApp
  , handlePApp
  , evalTr
  , evalTr'

  -- * Type families
  -- | The types of handlers are normalised when they are fused together, as are
  -- any results when a handler is applied. This normalisation removes unnecessary
  -- t`Identity`, t`Compose`, t`IdentityT`, and t`ComposeT` functors.
  , Apply
  , Assoc
  ) where

import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Handler
import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.Forward
