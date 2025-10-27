{-# LANGUAGE ExplicitNamespaces #-}
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
    type (!)
  , Progs
  , Prog
  , Effs (Eff, Effs)
  , call
  , callJ
  , callK
  , callM
  , callM'
  , weakenProg
  , progAlg
  , Effect
  , Identity

  -- * Operations
  , Member(..)
  , Members(..)
  , Injects( injs )
  , Append (..)

  -- * Algebras
  , Algebra
  , singAlgIso
  , (#)
  , weakenAlg
  , Forward (..)
  , Forwards (..)
  , ForwardsM (..)
  , ForwardsC (..)
  , absurdEffs
  , (#:)

  -- * Handler combinators
  , Handler (..)
  , runner
  , handler
  , handler'
  , identity
  , comp
  , weaken
  , hide
  , bypass
  , fromAT
  , interpret, interpretAT, interpretM
  , interpret1, interpretAT1, interpretM1
  , caseHdl
  , unionHdl
  , unscope
  , unscopes

  -- ** Fusion-based combinators
  , fuse, (|>)
  , pipe, (||>)
  , pass
  , generalFuse

  -- * Algebra transformers
  , AlgTrans (..)
  , asAT
  , idAT
  , compAT
  , weakenAT
  , algTrans1
  , fuseAT, fuseAT'
  , pipeAT
  , passAT
  , generalFuseAT


  -- * Evaluation
  , eval
  , handle
  , handleM
  , handleP
  , handleM'
  , handleP'
  , handleMApp
  , handlePApp
  , evalAT
  , evalAT'

  -- * Auxiliary types
  , Apply
  , Proxy (..)

  -- * Template Haskell
  , makeAlg, makeAlgType, makeAlgPattern, makeAlgSmart
  , makeScp, makeScpType, makeScpPattern, makeScpSmart
  ) where

import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Handler
import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Forward
import Control.Effect.Internal.TH
import Control.Effect.Family.Scoped
import Control.Effect.Family.Algebraic

import Data.Functor.Identity
import Data.List.Kind
import Data.Proxy