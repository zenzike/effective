{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

{-|
Module      : Staged.Handlers
Description : Staged handlers agree with the handlers they stage
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

Each staged handler @hC@ is spliced into an ordinary function, and tested to
agree with its unstaged handler @h@ on arbitrary programs. `writerIOC` and
the staged handlers of concurrency write to @stdout@ or fork threads, and
are only compiled, in `stagedIntro` and `stagedIntroFull` below.
-}
module Staged.Handlers (tests) where

import Control.Effect
import Control.Effect.State
import qualified Control.Effect.State.Lazy as Lazy
import Control.Effect.Reader
import Control.Effect.Writer
import qualified Control.Effect.Except as E
import Control.Effect.Nondet
import Control.Effect.Nondet.Operations (NondetOr, Once)
import qualified Control.Effect.Nondet.List as List
import qualified Control.Effect.Nondet.Logic as Logic
import Control.Effect.Concurrency
import Control.Effect.CodeGen

import qualified Data.Map as M
import Test.Tasty

import Effect.State (genState)
import Effect.Reader (genAsk, genReader)
import qualified Effect.Except as Except
import Effect.Nondet (genNondet, genNondetOr, genOnce)
import Effect.Concurrency (ActNames, bohem)
import Staged.Concur
import Law
import Gen

tests :: TestTree
tests = testGroup "Staged handlers"
  [ testGroup "state"
    [ law "stateC" $
        agree (genState @'[Put Int, Get Int]) (\s -> handle (state s))
          (\s p -> $$(handleC (stateC [||s||]) [||p||]))
    , law "stateC_" $
        agree (genState @'[Put Int, Get Int]) (\s -> handle (state_ s))
          (\s p -> $$(handleC (stateC_ [||s||]) [||p||]))
    , law "Lazy.stateC" $
        agree (genState @'[Put Int, Get Int]) (\s -> handle (Lazy.state s))
          (\s p -> $$(handleC (Lazy.stateC [||s||]) [||p||]))
    , law "Lazy.stateC_" $
        agree (genState @'[Put Int, Get Int]) (\s -> handle (Lazy.state_ s))
          (\s p -> $$(handleC (Lazy.stateC_ [||s||]) [||p||]))
    ]
  , testGroup "reader"
    [ law "readerC" $
        agree (genReader @'[Ask Int, Local Int]) (\r -> handle (reader r))
          (\r p -> $$(handleC (readerC [||r||]) [||p||]))
    , law "askerC" $
        agree (genAsk @'[Ask Int]) (\r -> handle (asker r))
          (\r p -> $$(handleC (askerC [||r||]) [||p||]))
    ]
    -- `writerC` and `writerC_` are not exported by the library, so they
    -- cannot be tested.
  , testGroup "exceptions"
      -- `exceptC` and `retryC` of "Control.Effect.Maybe" are not exported by
      -- the library, so they cannot be tested.
    [ law "Except.exceptC" $
        agree (Except.genExcept @'[E.Throw Int, E.Catch Int]) (\_ -> handle (E.except @Int))
          (\_ p -> $$(handleC (E.exceptC @Int) [||p||]))
    , law "Except.retryC" $
        agree (Except.genThrow @'[E.Throw Int, E.Catch Int]) (\_ -> handle (E.retry @Int))
          (\_ p -> $$(handleC (E.retryC @Int) [||p||]))
    ]
  , testGroup "nondeterminism"
    [ law "listC" $
        agree (genNondet @'[Empty, Choose]) (\_ -> handle list)
          (\_ p -> $$(handleC listC [||p||]))
    , law "logicC" $
        agree (genNondet @'[Empty, Choose]) (\_ -> handle logic)
          (\_ p -> $$(handleC logicC [||p||]))
    , law "List.nondetC" $
        agree (genNondetOr @'[Empty, NondetOr]) (\_ -> handle List.nondet)
          (\_ p -> $$(handleC List.nondetC [||p||]))
    , law "List.nondetC'" $
        agree (genNondet @'[Empty, Choose, NondetOr]) (\_ -> handle List.nondet')
          (\_ p -> $$(handleC List.nondetC' [||p||]))
    , law "List.backtrackC" $
        agree (genNondet <> genOnce @'[Empty, Choose, NondetOr, Once]) (\_ -> handle List.backtrack)
          (\_ p -> $$(handleC List.backtrackC [||p||]))
    , law "List.backtrackC'" $
        agree (genNondetOr <> genOnce @'[Empty, NondetOr, Once]) (\_ -> handle List.backtrack')
          (\_ p -> $$(handleC List.backtrackC' [||p||]))
    , law "Logic.nondetC" $
        agree (genNondetOr @'[Empty, NondetOr]) (\_ -> handle Logic.nondet)
          (\_ p -> $$(handleC Logic.nondetC [||p||]))
    , law "Logic.nondetC'" $
        agree (genNondet @'[Empty, Choose, NondetOr]) (\_ -> handle Logic.nondet')
          (\_ p -> $$(handleC Logic.nondetC' [||p||]))
    , law "Logic.backtrackC" $
        agree (genNondet <> genOnce @'[Empty, Choose, NondetOr, Once]) (\_ -> handle Logic.backtrack)
          (\_ p -> $$(handleC Logic.backtrackC [||p||]))
    , law "Logic.backtrackC'" $
        agree (genNondetOr <> genOnce @'[Empty, NondetOr, Once]) (\_ -> handle Logic.backtrack')
          (\_ p -> $$(handleC Logic.backtrackC' [||p||]))
    ]
  , testGroup "fusion"
    [ law "stateC |>$ Except.exceptC" $
        agree (genState <> Except.genExcept @'[Put Int, Get Int, E.Throw Int, E.Catch Int])
          (\s -> handle (state s |> E.except @Int))
          (\s p -> $$(handleC (stateC [||s||] |>$ E.exceptC @Int) [||p||]))
    , law "Except.exceptC |>$ stateC" $
        agree (genState <> Except.genExcept @'[E.Throw Int, E.Catch Int, Put Int, Get Int])
          (\s -> handle (E.except @Int |> state s))
          (\s p -> $$(handleC (E.exceptC @Int |>$ stateC [||s||]) [||p||]))
    ]
  ]

-- If we look at the handler code generated in the following example. We can
-- see that there are a lot unnecessary beta-reducible expressions. They are symptoms
-- caused by our choice of using `CodeQ (eff m -.> m)` to represent handler

stagedIntro :: IO (Either String ())
stagedIntro =
  $$(handleMFwdsC
    (Proxy @'[Par])
    ioParC
    (((threadIdC |>$ tellWithIdC) \\$ readerC [||""||])
       |>$ tellWithLockC
       |>$ ccsByQSemC @ActNames
       |>$ writerIOC)
    [|| bohem ||])


-- Fully staged

stagedIntroFull :: IO (Either String ())
stagedIntroFull = $$(stageHML (Proxy @'[Par]) (parGenIO :# genMAlg)
  ((ccsByQSemS @ActNames \\ reader (M.empty :: QSemMapS ActNames) \\ E.except @(CodeQ String)) |> writerGenIO)
  bohem)

{-
    do let childProc_airv
             = do x_airw <- putStrLn "Oh poor boy"
                  return ()
       forkIO childProc_airv
       x_airx <- QSem.newQSem 0
       x_airy <- QSem.newQSem 0
       x_airz <- QSem.newQSem 0
       x_airA <- QSem.newQSem 0
       let childProc_airB
             = do x_airC <- QSem.signalQSem x_airz
                  x_airD <- QSem.waitQSem x_airA
                  x_airE <- putStrLn "I need no sympathy"
                  return ()
       forkIO childProc_airB
       x_airF <- putStrLn "I am just a poor boy"
       x_airG <- QSem.waitQSem x_airz
       x_airH <- QSem.signalQSem x_airA
       return (Right ())
-}
