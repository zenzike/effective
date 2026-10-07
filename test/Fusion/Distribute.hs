{-# LANGUAGE DataKinds #-}

{-|
Module      : Fusion.Distribute
Description : Whether the operations of one effect distribute over another
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

The operations of one effect distribute over those of another when an
operation of the second can be moved out of an argument of an operation of
the first, as in @x * (y + z) = x * y + x * z@. When they do, the fusion is a
handler for the distributive tensor of the two theories.

Unlike "Fusion.Commute", this is not a grid over every pair of effects. A
distributive law copies the arguments that it does not move. The handlers of
nondeterminism in this library collect results in lists, which count copies,
so nothing distributes over choice. What does hold is that choice distributes
over an operation with no continuation, such as @throw@, when that operation
is handled last: the law then says that it absorbs the choice,
@throw \<|> m = throw = m \<|> throw@.
-}
module Fusion.Distribute (tests) where

import Control.Effect
import Control.Effect.State
import Control.Effect.Maybe
import Control.Effect.Nondet

import Test.Tasty
import Test.Tasty.HUnit

import Effect.Maybe (genThrow)
import Effect.Nondet (genNondet, genCoinAt)
import Law
import Gen

-- Whether the operations of the first effect distribute over those of the
-- second, for each order of fusion: @yes@ they do, @no@ they do not, @none@
-- there is no such fusion. These marks are a summary of the entries below
-- and must be kept in step with them. Pairs that are absent have not been
-- examined.
tests :: TestTree
tests = testGroup "Distribute"
  [ nondetOverExcept   -- list |> throw: yes    except |> list: no
  , stateOverNondet    -- state |> list: no     list |> state: no
  ]

-- Choice distributes over @throw@ when lists are handled first: a throw in
-- one branch ends every branch. The handler of exceptions has its @catch@
-- hidden, since @catch@ cannot be forwarded through lists.
nondetOverExcept :: TestTree
nondetOverExcept = testGroup "nondeterminism over exceptions"
  [ law "list |> throw" $
      distribute (genNondet <> genThrow) genCoinAt (genOperation genThrow) run

  , testCase "except |> list:  throw <|> m  is not  throw" $ do
      let run' = handle (except |> list)
      run' (throw <|> return (0 :: Int)) @?= [Nothing, Just 0]
      run' throw @?= [Nothing :: Maybe Int]
  ]
  where
    run :: Run '[Empty, Choose, Throw] (Maybe [Int])
    run _ = handle (list |> hide (Proxy @'[Catch]) except)

-- State does not distribute over choice in either order. Moving a choice out
-- of one branch of a @get@ makes a copy of the other branch, and a list of
-- results counts it twice.
stateOverNondet :: TestTree
stateOverNondet = testGroup "state over nondeterminism"
  [ testCase "state |> list:  get does not distribute over <|>" $ do
      let run = handle (state (0 :: Int) |> list)
      run inside  @?= [(0, 0)]
      run outside @?= [(0, 0), (0, 0)]
  , testCase "list |> state:  get does not distribute over <|>" $ do
      let run = handle (list |> state (0 :: Int))
      run inside  @?= ([0], 0)
      run outside @?= ([0, 0], 0)
  ]
  where
    -- The choice is in the branch of @get@ for the state @1@.
    inside, outside :: Members '[Get Int, Empty, Choose] effs => Prog effs Int
    inside  = get >>= \s -> if s == (1 :: Int) then return 1 <|> return 2 else return 0
    outside = (get >>= \s -> if s == (1 :: Int) then return 1 else return 0)
          <|> (get >>= \s -> if s == (1 :: Int) then return 2 else return 0)
