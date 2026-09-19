module Main where

import Hedgehog
import Hedgehog.Main

import Error
import Nondet
import State

main :: IO ()
main = defaultMain $ fmap checkParallel
  [ Error.examples
  , Nondet.examples
  , State.examples
  ]
