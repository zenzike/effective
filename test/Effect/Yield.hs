{-# LANGUAGE DataKinds #-}

{-|
Module      : Effect.Yield
Description : An example of coroutines by yielding
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental
-}
module Effect.Yield (tests) where

import Control.Effect
import Control.Effect.Writer
import Control.Effect.Yield

import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Yield"
  [ testCase "pingpong" $ do
      let (out, r) = pingpong
      r @?= Left 127
      words out @?= words "Ping 0. Pong 1. Ping 2. Pong 3. Ping 6. Pong 7. Ping 14."
                 ++ words "Pong 15. Ping 30. Pong 31. Ping 62. Pong 63. Ping 126. Too big."
  ]

ping :: Members '[Yield Int Int, Tell String] effs => Int -> Prog effs Int
ping n = do tell ("Ping " ++ show n ++ ". ")
            n' <- yield (n + 1)
            ping n'

pong :: Members '[Yield Int Int, Tell String] effs => Int -> Prog effs Int
pong n
  | n > 100   = do tell "Too big. "; return n
  | otherwise = do tell ("Pong " ++ show n ++ ". ")
                   n' <- yield (2 * n)
                   pong n'

pingpong :: (String, Either Int Int)
pingpong = handle
  (pingpongWith (pong @'[Yield Int Int, MapYield Int Int, Tell String]) |> writer @String)
  (ping 0)
