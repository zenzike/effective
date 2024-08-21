module Main where

import Hedgehog
import Hedgehog.Main

main :: IO ()
main = defaultMain $ fmap checkParallel
  [ 
  ]