```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}

module Nondet where

import Prelude hiding (or)

import Control.Effect
import Control.Handler
import Control.Effect.Cut
import Control.Effect.Nondet

import Hedgehog

knapsack
  :: Int -> [Int] -> Prog' '[Stop, Or] [Int]
knapsack w vs
  | w <  0    = stop
  | w == 0    = return []
  | otherwise = do v <- select vs
                   vs' <- knapsack (w - v) vs
                   return (v : vs')


-- `list` is not a modular handler and uses `eval` directly
example_Nondet1 :: Property
example_Nondet1 = property $ (list $ knapsack 3 [3, 2, 1] :: [[Int]])
  === [[3],[2,1],[1,2],[1,1,1]]

-- `nondet` is a modular handler but does not
-- handle `once`. Here it is immaterial because `once`
-- does not appear in the program
example_Nondet2 :: Property
example_Nondet2 = property $ (handle nondet $ knapsack 3 [3, 2, 1] :: [[Int]])
  === [[3],[2,1],[1,2],[1,1,1]]

-- `backtrack` is modular, and is furthermore simply
-- the joining of the nondet algebra with an algebra
-- for once
example_Nondet3 :: Property
example_Nondet3 = property $ (handle backtrack $ knapsack 3 [3, 2, 1] :: [[Int]])
  === [[3],[2,1],[1,2],[1,1,1]]

-- onceEx :: (Member Or sig, Member Once sig) => Prog sig I
example_Once :: Property
example_Once = property $ handle onceNondet p === [1, 2]
  where
    p :: Members '[Or, Once] sig => Prog sig Int
    p = do
      x <- once (or (return 0) (return 5))
      or (return (x + 1)) (return (x + 2))
-- ghci> exampleOnce
-- [1,2]
example_Once' :: Property
example_Once' = property $ handle onceNondet p === [1, 2] where
  p :: Members '[Or, Once] sig => Prog sig Int
  p = do x <- once (or (return 0) (return 5))
         or (return (x + 1)) (return (x + 2))
-- ghci> exampleOnce'
-- [1,2]
example_Once'' :: Property
example_Once'' = property $ handle onceNondet p === [1, 2] where
  p :: Members '[Or, Once] sig => Prog sig Int
  p = do x <- once (or (return 0) (return 5))
         or (return (x + 1)) (return (x + 2))

example_Once''' :: Property
example_Once''' = property $ handle onceNondet p === [1, 2] where
  p :: Members '[Or, Once] sig => Prog sig Int
  p = do x <- once (or (return 0) (return 5))
         or (return (x + 1)) (return (x + 2))

examples :: Group
examples = $$(discoverPrefix "example_")
```haskell
