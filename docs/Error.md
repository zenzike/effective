```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}

module Error where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Effect
import Control.Handler
import Control.Effect.Maybe

monus :: Int -> Int -> Prog' '[Throw] Int
monus x y = do if x < y then throw else return (x - y)

safeMonus :: Int -> Int -> Prog '[Throw, Catch] Int
safeMonus x y = catch (monus x y) (return 0)

example_monus :: Property
example_monus = property $ do
  x <- forAll $ Gen.int $ Range.linear 1 1000
  y <- forAll $ Gen.int $ Range.linear 1 1000

  if (x < y)
    then handle except (monus x y) === Nothing
    else handle except (monus x y) === Just (x - y)

example_safeMonus :: Property
example_safeMonus = property $ do
  x <- forAll $ Gen.int $ Range.linear 1 1000
  y <- forAll $ Gen.int $ Range.linear 1 1000

  if (x < y)
    then handle except (safeMonus x y) === Just 0
    else handle except (safeMonus x y) === Just (x - y)

examples :: Group
examples = $$(discoverPrefix "example_")
```
