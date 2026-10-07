{-# LANGUAGE DataKinds #-}

{-|
Module      : Fusion.Sum
Description : The laws of each effect under fusions of handlers
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

A fusion of two handlers respects the equations of each of its parts, so it
is a handler for the sum of the two theories.
-}
module Fusion.Sum (tests) where

import Prelude hiding (sum)

import Control.Effect
import Control.Effect.State
import Control.Effect.Reader
import Control.Effect.Writer
import Control.Effect.Maybe
import qualified Control.Effect.Except as E
import Control.Effect.Nondet

import Test.Tasty

import qualified Effect.State as State
import qualified Effect.Reader as Reader
import qualified Effect.Writer as Writer
import qualified Effect.Maybe as Maybe
import qualified Effect.Except as Except
import qualified Effect.Nondet as Nondet
import Law

tests :: TestTree
tests = testGroup "Sum"
  [ readerWriter, readerState, readerExcept, readerNondet
  ,               writerState, writerExcept, writerNondet
  ,                            stateExcept,  stateNondet
  ,                                          exceptNondet
  ]

readerWriter :: TestTree
readerWriter = testGroup "reader/writer"
  [ testGroup "reader |> writer" $
      sum Reader.theory Writer.theory (\r -> handle (reader r |> writer @[Int]))
  , testGroup "writer |> reader" $
      sum Writer.theory Reader.theory (\r -> handle (writer @[Int] |> reader r))
  , testGroup "reader |> censors |> writer" $
      sum Reader.theory Writer.censorTheory
        (\r -> handle (reader r |> censors @[Int] (map (+ r)) |> writer @[Int]))
  , testGroup "censors |> writer |> reader" $
      sum Writer.censorTheory Reader.theory
        (\r -> handle (censors @[Int] (map (+ r)) |> writer @[Int] |> reader r))
  ]

readerState :: TestTree
readerState = testGroup "reader/state"
  [ testGroup "reader |> state" $
      sum Reader.theory State.theory (\s -> handle (reader s |> state s))
  , testGroup "state |> reader" $
      sum State.theory Reader.theory (\s -> handle (state s |> reader s))
  ]

readerExcept :: TestTree
readerExcept = testGroup "reader/exceptions"
  [ testGroup "reader |> except" $
      sum Reader.theory Maybe.theory (\r -> handle (reader r |> except))
  , testGroup "except |> reader" $
      sum Maybe.theory Reader.theory (\r -> handle (except |> reader r))
  ]

readerNondet :: TestTree
readerNondet = testGroup "reader/nondeterminism"
  [ testGroup "reader |> list" $
      sum Reader.theory Nondet.theory (\r -> handle (reader r |> list))
  , testGroup "list |> reader" $
      sum Nondet.theory Reader.theory (\r -> handle (list |> reader r))
  ]

writerState :: TestTree
writerState = testGroup "writer/state"
  [ testGroup "writer |> state" $
      sum Writer.theory State.theory (\s -> handle (writer @[Int] |> state s))
  , testGroup "state |> writer" $
      sum State.theory Writer.theory (\s -> handle (state s |> writer @[Int]))
  , testGroup "censors |> writer |> state" $
      sum Writer.censorTheory State.theory
        (\s -> handle (censors @[Int] (map (+ s)) |> writer @[Int] |> state s))
  , testGroup "state |> censors |> writer" $
      sum State.theory Writer.censorTheory
        (\s -> handle (state s |> censors @[Int] (map (+ s)) |> writer @[Int]))
  ]

writerExcept :: TestTree
writerExcept = testGroup "writer/exceptions"
  [ testGroup "writer |> except" $
      sum Writer.theory Maybe.theory (\_ -> handle (writer @[Int] |> except))
  , testGroup "except |> writer" $
      sum Maybe.theory Writer.theory (\_ -> handle (except |> writer @[Int]))
  , testGroup "censors |> writer |> except" $
      sum Writer.censorTheory Maybe.theory
        (\n -> handle (censors @[Int] (map (+ n)) |> writer @[Int] |> except))
  , testGroup "except |> censors |> writer" $
      sum Maybe.theory Writer.censorTheory
        (\n -> handle (except |> censors @[Int] (map (+ n)) |> writer @[Int]))
  ]

writerNondet :: TestTree
writerNondet = testGroup "writer/nondeterminism"
  [ testGroup "writer |> list" $
      sum Writer.theory Nondet.theory (\_ -> handle (writer @[Int] |> list))
  , testGroup "list |> writer" $
      sum Nondet.theory Writer.theory (\_ -> handle (list |> writer @[Int]))
  , testGroup "censors |> writer |> list" $
      sum Writer.censorTheory Nondet.theory
        (\n -> handle (censors @[Int] (map (+ n)) |> writer @[Int] |> list))
  , testGroup "list |> censors |> writer" $
      sum Nondet.theory Writer.censorTheory
        (\n -> handle (list |> censors @[Int] (map (+ n)) |> writer @[Int]))
  ]

stateExcept :: TestTree
stateExcept = testGroup "state/exceptions"
  [ testGroup "state |> except" $
      sum State.theory Maybe.theory (\s -> handle (state s |> except))
  , testGroup "except |> state" $
      sum Maybe.theory State.theory (\s -> handle (except |> state s))
  , testGroup "state |> Except.except" $
      sum State.theory Except.theory (\s -> handle (state s |> E.except @Int))
  , testGroup "Except.except |> state" $
      sum Except.theory State.theory (\s -> handle (E.except @Int |> state s))
  , testGroup "retry |> state" $
      sum Maybe.retryTheory State.theory (\s -> handle (retry |> state s))
  , testGroup "Except.retry |> state" $
      sum Except.retryTheory State.theory (\s -> handle (E.retry @Int |> state s))
  ]

stateNondet :: TestTree
stateNondet = testGroup "state/nondeterminism"
  [ testGroup "state |> list" $
      sum State.theory Nondet.theory (\s -> handle (state s |> list))
  , testGroup "list |> state" $
      sum Nondet.theory State.theory (\s -> handle (list |> state s))
  ]

exceptNondet :: TestTree
exceptNondet = testGroup "exceptions/nondeterminism"
  [ testGroup "except |> list" $
      sum Maybe.theory Nondet.theory (\_ -> handle (except |> list))
  ]
