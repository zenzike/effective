```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Nondet where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Nondet.Alternative
import Control.Effect.Nondet.Cut
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Nondet.List
import Control.Effect.Nondet

import Control.Monad (guard)


import Hedgehog hiding (eval)

knapsack
  :: Int -> [Int] -> [Int] ! [Empty, Choose]
knapsack w vs
  | w <  0    = empty
  | w == 0    = return []
  | otherwise = do v <- select vs
                   vs' <- knapsack (w - v) vs
                   return (v : vs')

example_Nondet1 :: Property
example_Nondet1 = property $ (handle list $ knapsack 3 [3, 2, 1] :: [[Int]])
  === [[3],[2,1],[1,2],[1,1,1]]

-- | `list` evaluates a nondeterministic computation and collects all results
-- into a list. It handles the t`Empty`, t`Choose`, and t`Once` effects.
list' :: Prog [Empty, Choose, Once] a -> [a]
list' = eval halg where
  halg :: Algebra [Empty, Choose, Once] []
  halg = (\Empty -> []) :#
         (\(Choose xs ys) -> xs ++ ys) :#.
         (\(Once xs) -> case xs of [] -> []; (x:xs) -> [x])

-- `list'` is not a modular handler and uses `eval` directly
example_Nondet1' :: Property
example_Nondet1' = property $ (list' $ knapsack 3 [3, 2, 1] :: [[Int]])
  === [[3],[2,1],[1,2],[1,1,1]]


-- `nondet` is a modular handler but does not handle `once`. Here it is
-- immaterial because `once` does not appear in the program,
-- however it requires `choose` to be algebraic.

example_Nondet2 :: Property
example_Nondet2 = property $ (handle (chooseByNondet |> nondet) $ knapsack 3 [3, 2, 1] :: [[Int]])
  === [[3],[2,1],[1,2],[1,1,1]]

-- `backtrack` is modular, and is furthermore simply
-- the joining of the nondet algebra with an algebra
-- for once
example_backtrack1 :: Property
example_backtrack1 = property $ (handle backtrack $ knapsack 3 [3, 2, 1] :: [[Int]])
  === [[3],[2,1],[1,2],[1,1,1]]

example_backtrack2 :: Property
example_backtrack2 = property $ handle backtrack p === [1, 2] where
  p :: (Alternative (Prog effs), Members '[Once] effs) => Prog effs Int
  p = do x <- once (return 0 <|> return 5)
         (return (x + 1)) <|> (return (x + 2))
-- ghci> exampleOnce
-- [1,2]

example_Once' :: Property
example_Once' = property $ handle onceNondet p === [1, 2] where
  p :: Members '[Choose, Empty, Once] effs => Prog effs Int
  p = do x <- once ((return 0) <|> (return 5))
         (return (x + 1)) <|> (return (x + 2))
-- ghci> exampleOnce'
-- [1,2]

example_Once'' :: Property
example_Once'' = property $ handle onceNondet p === [1, 2] where
  p :: Members '[Choose, Empty, Once] effs => Prog effs Int
  p = do x <- once ((return 0) <|> (return 5))
         (return (x + 1)) <|> (return (x + 2))

example_Once''' :: Property
example_Once''' = property $ handle onceNondet p === [1, 2] where
  p :: Members '[Choose, Empty, Once] effs => Prog effs Int
  p = do x <- once ((return 0) <|> (return 5))
         (return (x + 1)) <|> (return (x + 2))

-- queens n = [c_1, c_2, ... , c_n] where
--   (i, c_i) is the (row, column) of a queen
queens :: Int -> [Int] ! [Empty, Choose]
queens n = go [1 .. n] []
  where
    -- `go cs qs` searches the rows `cs` for queens that do
    -- not threaten the queens in `qs`
    go :: [Int] -> [Int] -> [Int] ! [Empty, Choose]
    go [] qs =  return qs
    go cs qs =  do (c, cs') <- selects cs
                   guard (noThreat qs c 1)
                   go cs' (c:qs)

    -- `noThreat qs r c` returns `True` if there is no threat
    -- from a queen in `qs` to the square given by `(r, c)`.
    noThreat :: [Int] -> Int -> Int -> Bool
    noThreat []      c r  = True
    noThreat (q:qs)  c r  = abs (q - c) /= r && noThreat qs c (r+1)

example_queens = property $
  length (handle list (queens 8)) === 92

examples :: Group
examples = $$(discoverPrefix "example_")
```haskell
