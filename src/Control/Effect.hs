{-|
Module      : Control.Effect
Description : Main module for the effective library
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module contains the core types and functions for working with effects.
The README file contains a tutorial on how to use this library.
-}
{-# LANGUAGE ExplicitNamespaces, CPP, MagicHash #-}

module Control.Effect
  ( -- * Programs
    Prog
  , type (!)
  , WithName, (:@)
  , call,  callJ,  callK
  , callM, callJM, callKM
  , callMC
  , callP
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
  , callN
#endif
  , weakenProg
  , progAlg
  , Effect
  , Identity

  -- * Operations
  , Member(..)
  , Members(..)
  , KnownEffs(..)
  , dispatch
  , dispatchC
  , dispatchCases

  -- * Algebras
  , Algebra, Algebra_, AlgebraArray
  , Case, Case_
  , singAlgIso, singAlg
  , (#)
  , emptyAlg, pattern (:#), pattern (:#.)
  , emptyCase, pattern (:%), pattern (:%.)
  , Forward (..)
  , Forwards (..)
  , ForwardsM (..)
  , ForwardsC (..)

  -- * Handler combinators
  , Handler (..)
  , HandlerC (..)
  , handler
  , handler'
  , Runner (..)
  , RunnerC (..)
  , runner'
  , (<:)
  , fromRunner
  , identity
  , comp
  , weaken
  , hide
  , withFwds
  , interpret, interpretAT, interpretM, interpretMC
  , interpret1, interpretAT1, interpretM1, interpretM1C
  , caseHdl
  , unionHdl, unionHdlAT

  -- ** Fusion-based combinators
  , fuse, (|>)
  , fuseApp, (++>)
  , fuseC, (|>$)
  , fuseAppC, (++>$)
  , pipe, (\\), pipeC, (\\$)
  , pass
  , generalFuse

  -- * Algebra transformers
  , AlgTrans (..)
  , AlgTransC (..)
  , asAT
  , idAT
  , compAT
  , weakenAT
  , algTrans1, algTrans1C
  , algTrans'
  , fuseAT, fuseAT'
  , fuseATC
  , pipeAT
  , passAT
  , generalFuseAT


  -- * Evaluation
  , eval
  , handle
  , handleC, handleM
  , handleP, ProgAlg#
  , handleM'
  , handleP'
  , handleMFwds, handleMFwdsC
  , handleMApp
  , handlePApp
  , evalAT
  , evalAT'
  , renameEffs, renameEffsAT
  , renameOEffs, renameOEffsAT

  -- * Auxiliary types
  , Apply
  , Proxy (..)

  -- * Lightweight staging
  , CodeQ
  , AlgebraC (..)
  , emptyCaseC
  , emptyAlgC
  , (#$), pattern (:#.$)
  , NatTrans (..), type (-.>)
  , unionAlgC, appendAlgC
  , genAlgebra

  -- * Template Haskell
  , type (~>)
  , makeGen
  , makeAlg
  , makeScp
  ) where

import Control.Effect.Internal.Prog
import Control.Effect.Internal.Algebra
import Control.Effect.Internal.Handler
import Control.Effect.Internal.Runner
import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Forward
import Control.Effect.WithName
import Control.Effect.Internal.TH
import Control.Effect.Family.Scoped
import Control.Effect.Family.Algebraic

import Data.Functor.Identity
import Data.List.Kind
import Data.Proxy
