{-# LANGUAGE DataKinds, QualifiedDo #-}

{-|
Module      : Internal.Do
Description : Do-notation for fusing handlers
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

A do-block of handlers under "Control.Effect.Do" is the same as the chain of
`|>` it desugars to. 
-}
module Internal.Do (tests) where

import Control.Effect
import Control.Effect.Reader
import Control.Effect.Writer
import Control.Effect.State
import Control.Effect.Maybe
import Control.Effect.Nondet
import qualified Control.Effect.Do as H

import Test.Tasty
import Test.Tasty.HUnit

import Effect.Reader (genReader)
import Effect.Writer (genWriter, genCensor)
import Effect.State (genState)
import Effect.Maybe (genExcept)
import Effect.Nondet (genNondet)
import Law

tests :: TestTree
tests = testGroup "Do"
  [ testCase "H.do { reader; censors \\\\ writer; state; except; list }" $
      handle (H.do reader (1 :: Int)
                   censors @[Int] (map (+ 1)) \\ writer @[Int]
                   state (10 :: Int)
                   except
                   list) prog
      @?= [ Just (([21], 1), 11), Just (([21], 10), 11) ]

  , law "H.do { reader; censors \\\\ writer; state; except; list }  =  the |> chain" $
      agree (genReader <> genWriter <> genCensor <> genState <> genExcept <> genNondet
               @'[Ask Int, Local Int, Tell [Int], Censor [Int], Get Int, Put Int, Throw, Catch, Empty, Choose])
        (\n -> handle (reader n |> (censors @[Int] (map (+ n)) \\ writer @[Int])
                                |> state n |> except |> list))
        (\n -> handle (H.do reader n
                            censors @[Int] (map (+ n)) \\ writer @[Int]
                            state n
                            except
                            list))
  ]

prog :: Members '[Ask Int, Tell [Int], Censor [Int], Get Int, Put Int, Throw, Catch, Empty, Choose] effs
     => Prog effs Int
prog = do r <- ask
          n <- get
          put (n + r)
          censor @[Int] (map (* 2)) (tell [n])
          x <- return r <|> return n
          catch (do tell [x]; throw) (return ())
          return x
