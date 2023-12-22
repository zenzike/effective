{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Nondet where

import Control.Effect
import Control.Effect.Nondet
import Control.Effect ( Members, Prog, Prog' )
import Control.Handler
import Control.Effect.Nondet ( Stop, Or, or, list, stop )
import Data.List (sort)

import Control.Monad.Trans.Class

import Prelude hiding (or)

import Hedgehog ( MonadGen, Property, property, discover, Group, (===), forAll, diff )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

tree :: Prog '[Stop, Or, Once] Int
tree = or (or (return 1)
              (or (return 3)
                  (return 4)))
          (or (return 2)
              (or (return 5)
                  (return 6)))

prop_list :: Property
prop_list = property $
  sort (list tree) === [1 .. 6]

-- genNondet :: (Members '[Or, Stop] sig, MonadGen m) => m (Prog sig Int)
genNondet :: (MonadGen m) => m (Prog '[Stop, Or, Once] Int)
genNondet = Gen.recursive Gen.choice
   [ pure (stop :: Prog '[Stop, Or, Once] Int)
   , return <$> Gen.int (Range.linear 0 100)
   , once <$> genNondet ]
   [ or <$> genNondet <*> genNondet ]

prop_list' :: Property
prop_list' = property $ do
  tree <- forAll genNondet
  list tree === handle backtrack (tree)

prop_once :: Property
prop_once = property $ do
  tree <- forAll genNondet
  diff (length (handle backtrack (once (tree)))) (<=) 1

props :: Group
props = $$(discover)
