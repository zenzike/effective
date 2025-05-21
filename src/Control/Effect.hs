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
  , Identity

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
  , ForwardsM (..)
  , ForwardsC (..)
  , absurdEffs

  -- * Handler combinators
  , Handler (..)
  , handler
  , handler'
  , identity
  , comp
  , weaken
  , hide
  , bypass
  , fromAT
  , interpret, interpretAT
  , interpret1, interpretAT1
  , interpretM
  , caseHdl
  , unionHdl

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
  , evalTr
  , evalTr'

  -- * Auxiliary types
  , Apply
  , Proxy (..)
  ) where

import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Handler
import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Forward
import Data.Functor.Identity
import Data.List.Kind
import Data.Proxy