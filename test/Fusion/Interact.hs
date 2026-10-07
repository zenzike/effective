{-# LANGUAGE DataKinds #-}

{-|
Module      : Fusion.Interact
Description : Equations between two effects other than commutativity
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

A fusion of two handlers may satisfy equations between the two effects that
are neither commutativity, tested in "Fusion.Commute", nor distributivity, tested in
"Fusion.Distribute".
-}
module Fusion.Interact (tests) where

import Control.Effect
import Control.Effect.State
import Control.Effect.Writer
import Control.Effect.Maybe
import Control.Effect.Nondet

import Hedgehog
import Test.Tasty

import Effect.State (genState)
import Effect.Writer (genWriter)
import Effect.Maybe (genExcept)
import Effect.Nondet (genNondet)
import Law
import Gen

tests :: TestTree
tests = testGroup "Interact"
  [ stateExcept
  , stateNondet
  , writerExcept
  , writerNondet
  ]

-- A state handled first is rolled back by a catch, and one handled last is
-- kept.
stateExcept :: TestTree
stateExcept = testGroup "state/exceptions"
  [ law "state |> except:  catch (m >> throw) h  =  h" $ do
      m <- forAllM genState
      h <- forAllM (genState <> genExcept)
      equal (genState <> genExcept) (\s -> handle (state s |> except)) (catch (m >> throw) h) h
  , law "except |> state:  catch (m >> throw) h  =  m >> h" $ do
      m <- forAllM genState
      h <- forAllM (genState <> genExcept)
      equal (genState <> genExcept) (\s -> handle (except |> state s)) (catch (m >> throw) h) (m >> h)
  ]

-- A state handled first is discarded by a failure and copied into each branch
-- of a choice. A state handled last is shared by the branches, which is the
-- put-or law of global state.
stateNondet :: TestTree
stateNondet = testGroup "state/nondeterminism"
  [ law "state |> list:  m >> empty  =  empty" $ do
      m <- forAllM (genState <> genNondet)
      equal (genState <> genNondet) (\s -> handle (state s |> list)) (m >> empty) empty
    -- Here @m@ uses state alone. A list of results is ordered, so the two
    -- sides differ in order when @m@ itself makes choices.
  , law "state |> list:  m >>= \\x -> k x <|> k' x  =  (m >>= k) <|> (m >>= k')" $ do
      m  <- forAllM genState
      k  <- forAllK (genState <> genNondet)
      k' <- forAllK (genState <> genNondet)
      equal (genState <> genNondet) (\s -> handle (state s |> list))
        (m >>= \x -> k x <|> k' x)
        ((m >>= k) <|> (m >>= k'))

  , law "list |> state:  (put s >> m) <|> n  =  put s >> (m <|> n)" $ do
      s <- forAll genInt
      m <- forAllM (genState <> genNondet)
      n <- forAllM (genState <> genNondet)
      equal (genState <> genNondet) (\s0 -> handle (list |> state s0))
        ((put s >> m) <|> n)
        (put s >> (m <|> n))
  ]

writerExcept :: TestTree
writerExcept = testGroup "writer/exceptions"
  [ law "writer |> except:  catch (tell w >> throw) h  =  h" $ do
      w <- forAll genInts
      h <- forAllM (genWriter <> genExcept)
      equal (genWriter <> genExcept) (\_ -> handle (writer @[Int] |> except))
        (catch (tell w >> throw) h) h
  , law "except |> writer:  catch (tell w >> throw) h  =  tell w >> h" $ do
      w <- forAll genInts
      h <- forAllM (genWriter <> genExcept)
      equal (genWriter <> genExcept) (\_ -> handle (except |> writer @[Int]))
        (catch (tell w >> throw) h) (tell w >> h)
  ]

writerNondet :: TestTree
writerNondet = testGroup "writer/nondeterminism"
  [ law "writer |> list:  tell w >> empty  =  empty" $ do
      w <- forAll genInts
      equal (genWriter <> genNondet) (\_ -> handle (writer @[Int] |> list))
        (tell w >> empty) empty
  , law "list |> writer:  (tell w >> m) <|> n  =  tell w >> (m <|> n)" $ do
      w <- forAll genInts
      m <- forAllM (genWriter <> genNondet)
      n <- forAllM (genWriter <> genNondet)
      equal (genWriter <> genNondet) (\_ -> handle (list |> writer @[Int]))
        ((tell w >> m) <|> n) (tell w >> (m <|> n))
  ]
