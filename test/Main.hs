module Main where

import Hedgehog
import Hedgehog.Main

import Nondet

main :: IO ()
main = defaultMain $ fmap checkParallel
  [ Nondet.props ]