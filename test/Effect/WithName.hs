{-# LANGUAGE CPP #-}

{-|
Module      : Effect.WithName
Description : Tests of named effects
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental
-}
module Effect.WithName (tests) where

import Control.Effect
import Control.Effect.State
import Control.Effect.WithName

import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "WithName"
  [ testCase "two named states, by proxy" $ fibP @?= 21
  , testCase "two named states, by name"  $ fibN @?= 21
  ]

type Effs = ["a" :@ Put Int, "a" :@ Get Int, "b" :@ Put Int, "b" :@ Get Int]

a :: Proxy "a"
a = Proxy

b :: Proxy "b"
b = Proxy

fib :: Int -> Int ! Effs
fib 0 = getP b
fib n = do sA <- getP a
           sB <- getP b
           putP b (sA + sB)
           putP a (sB :: Int)
           fib (n - 1)

fibP :: Int
fibP = handle
        (renameEffs a (state_ (0 :: Int))
          |> renameEffs b (state_ (1 :: Int)))
        (fib 7)

#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
-- A version of @fib@ that uses @getN@/@putN@.
fib' :: Int -> Int ! Effs
fib' 0 = getN "b"
fib' n = do sA <- getN "a"
            sB <- getN "b"
            putN "b" (sA + sB)
            putN "a" (sB :: Int)
            fib' (n - 1)
#else
fib' = fib
#endif

fibN :: Int
fibN = handle
        (renameEffs a (state_ (0 :: Int))
          |> renameEffs b (state_ (1 :: Int)))
        (fib' 7)
