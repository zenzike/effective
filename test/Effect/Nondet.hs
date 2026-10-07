{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{-|
Module      : Effect.Nondet
Description : Laws and examples for nondeterminism
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}
module Effect.Nondet
  ( tests, theory, laws, onceLaws
  , genNondet, genNondetOr, genCut, genOnce, genCoinAt, failure
  ) where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Nondet
import Control.Effect.Nondet.Operations
import qualified Control.Effect.Nondet.List as List
import qualified Control.Effect.Nondet.Logic as Logic
import Control.Effect.Nondet.Cut
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Monad (guard)

import Hedgehog (Gen, forAll)
import qualified Hedgehog.Gen as Gen
import Test.Tasty
import Test.Tasty.HUnit

import Law
import Gen

tests :: TestTree
tests = testGroup "Nondet"
  [ testGroup "laws of choose"
    [ testGroup "list"             $ laws genNondet (\_ -> handle list)
    , testGroup "logic"            $ laws genNondet (\_ -> handle logic)
    , testGroup "List.nondet'"     $ laws genNondet (\_ -> handle List.nondet')
    , testGroup "List.backtrack"   $ laws genNondet (\_ -> handle List.backtrack)
    , testGroup "Logic.nondet'"    $ laws genNondet (\_ -> handle Logic.nondet')
    , testGroup "Logic.backtrack"  $ laws genNondet (\_ -> handle Logic.backtrack)
    , testGroup "cutList"          $ laws genNondet (\_ -> handle cutList)
    , testGroup "onceNondet"       $ laws genNondet (\_ -> handle onceNondet)
    ]
  , testGroup "laws of nondetOr, by chooseByNondet"
    [ testGroup "List.nondet"      $ laws genNondet (\_ -> handle (chooseByNondet |> List.nondet))
    , testGroup "List.nondet'"     $ laws genNondet (\_ -> handle (chooseByNondet |> List.nondet'))
    , testGroup "List.backtrack"   $ laws genNondet (\_ -> handle (chooseByNondet |> List.backtrack))
    , testGroup "List.backtrack'"  $ laws genNondet (\_ -> handle (chooseByNondet |> List.backtrack'))
    , testGroup "Logic.nondet"     $ laws genNondet (\_ -> handle (chooseByNondet |> Logic.nondet))
    , testGroup "Logic.nondet'"    $ laws genNondet (\_ -> handle (chooseByNondet |> Logic.nondet'))
    , testGroup "Logic.backtrack"  $ laws genNondet (\_ -> handle (chooseByNondet |> Logic.backtrack))
    , testGroup "Logic.backtrack'" $ laws genNondet (\_ -> handle (chooseByNondet |> Logic.backtrack'))
    , testGroup "cutList"          $ laws genNondet (\_ -> handle (chooseByNondet |> cutList))
    , testGroup "nondetByChoose |> list" $
        laws genNondet (\_ -> handle (chooseByNondet |> nondetByChoose |> list))
    ]
  , testGroup "laws of once"
    [ testGroup "List.backtrack"   $ onceLaws (genNondet <> genOnce) (\_ -> handle List.backtrack)
    , testGroup "Logic.backtrack"  $ onceLaws (genNondet <> genOnce) (\_ -> handle Logic.backtrack)
    , testGroup "onceNondet"       $ onceLaws (genNondet <> genOnce) (\_ -> handle onceNondet)
    , testGroup "List.backtrack'"  $
        onceLaws (genNondet <> genOnce) (\_ -> handle (chooseByNondet |> List.backtrack'))
    , testGroup "Logic.backtrack'" $
        onceLaws (genNondet <> genOnce) (\_ -> handle (chooseByNondet |> Logic.backtrack'))
    ]
  , testGroup "laws of cut"
    [ testGroup "cutList"    $ cutLaws (genNondet <> genCut) (\_ -> handle cutList)
    , testGroup "onceNondet" $ cutLaws (genNondet <> genCut) (\_ -> handle onceNondet)
    , law "onceNondet:  once m  =  cutCall (m >>= \\x -> cut >> return x)" $ do
        let g = genNondet <> genCut <> genOnce
        m <- forAllM g
        equal g (\_ -> handle onceNondet)
          (once m) (cutCall (m >>= \x -> cut >> return x))
    ]
  , testGroup "handlers agree"
    [ law "list, logic" $
        agree (genNondet @'[Empty, Choose]) (\_ -> handle list) (\_ -> handle logic)
    , law "list, List.nondet'" $
        agree (genNondet @'[Empty, Choose]) (\_ -> handle list) (\_ -> handle List.nondet')
    , law "list, Logic.nondet'" $
        agree (genNondet @'[Empty, Choose]) (\_ -> handle list) (\_ -> handle Logic.nondet')
    , law "list, cutList" $
        agree (genNondet @'[Empty, Choose]) (\_ -> handle list) (\_ -> handle cutList)
    , law "list, chooseByNondet |> List.nondet" $
        agree (genNondet @'[Empty, Choose]) (\_ -> handle list) (\_ -> handle (chooseByNondet |> List.nondet))
    , law "list, the algebra list'" $
        agree (genNondet @'[Empty, Choose]) (\_ -> handle list) (\_ -> list')
    , law "List.nondet, Logic.nondet" $
        agree (genNondetOr @'[Empty, NondetOr]) (\_ -> handle List.nondet) (\_ -> handle Logic.nondet)
    , law "List.nondet, nondetByChoose |> list" $
        agree (genNondetOr @'[Empty, NondetOr]) (\_ -> handle List.nondet) (\_ -> handle (nondetByChoose |> list))
    , law "List.backtrack, Logic.backtrack" $
        agree (genNondet <> genOnce @'[Empty, Choose, Once]) (\_ -> handle List.backtrack) (\_ -> handle Logic.backtrack)
    , law "List.backtrack, onceNondet" $
        agree (genNondet <> genOnce @'[Empty, Choose, Once]) (\_ -> handle List.backtrack) (\_ -> handle onceNondet)
    , law "List.backtrack', Logic.backtrack'" $
        agree (genNondetOr <> genOnce @'[Empty, NondetOr, Once])
          (\_ -> handle List.backtrack') (\_ -> handle Logic.backtrack')
    ]
  , examples
  ]

-- | Failure, for rows that have `Empty` but may not have `Choose`.
failure :: Member Empty effs => Prog effs a
failure = call (Alg Empty_)

genNondet :: Members '[Empty, Choose] effs => GenProg effs
genNondet = genAlg [const failure] <> GenProg (\sub ->
  [ Gen.subterm2 sub sub (\p q env -> p env <|> q env) ])

-- | Nondeterminism with the algebraic choice `nondetOr`.
genNondetOr :: Members '[Empty, NondetOr] effs => GenProg effs
genNondetOr = genAlg [const failure] <> GenProg (\sub ->
  [ Gen.subterm2 sub sub (\p q env -> nondetOr (p env) (q env)) ])

genCut :: Members '[CutFail, CutCall] effs => GenProg effs
genCut = genAlg [const cutFail] <> GenProg (\sub -> [ Gen.subterm sub (cutCall .) ])

genOnce :: Member Once effs => GenProg effs
genOnce = GenProg $ \sub -> [ Gen.subterm sub (once .) ]

theory :: (Members '[Empty, Choose] effs, Eq b, Show b) => Theory effs b
theory = Theory "nondeterminism" genNondet laws

-- | A coin that returns one of two different numbers, and one of the two.
genCoinAt :: Members '[Empty, Choose] effs => Gen (Prog effs Int, Int)
genCoinAt = do
  x <- genInt
  y <- Gen.filter (/= x) genInt
  b <- Gen.element [x, y]
  return (return x <|> return y, b)

laws :: (Members '[Empty, Choose] effs, Eq b, Show b)
     => GenProg effs -> Run effs b -> [TestTree]
laws g run =
  [ law "empty <|> m  =  m" $ do
      m <- forAllM g
      equal g run (empty <|> m) m
  , law "m <|> empty  =  m" $ do
      m <- forAllM g
      equal g run (m <|> empty) m
  , law "(m <|> n) <|> o  =  m <|> (n <|> o)" $ do
      m <- forAllM g
      n <- forAllM g
      o <- forAllM g
      equal g run ((m <|> n) <|> o) (m <|> (n <|> o))
  , law "empty >>= k  =  empty" $ do
      k <- forAllK g
      equal g run (empty >>= k) empty
  , law "(m <|> n) >>= k  =  (m >>= k) <|> (n >>= k)" $ do
      m <- forAllM g
      n <- forAllM g
      k <- forAllK g
      equal g run ((m <|> n) >>= k) ((m >>= k) <|> (n >>= k))
  ]

cutLaws :: (Members '[Empty, Choose, CutFail, CutCall] effs, Eq b, Show b)
        => GenProg effs -> Run effs b -> [TestTree]
cutLaws g run =
  [ law "cutFail >>= k  =  cutFail" $ do
      k <- forAllK g
      equal g run (cutFail >>= k) cutFail
  , law "cutFail <|> m  =  cutFail" $ do
      m <- forAllM g
      equal g run (cutFail <|> m) cutFail
  , law "(m <|> cutFail) <|> n  =  m <|> cutFail" $ do
      m <- forAllM g
      n <- forAllM g
      equal g run ((m <|> cutFail) <|> n) (m <|> cutFail)
  , law "cutCall cutFail  =  empty" $
      equal g run (cutCall cutFail) empty
  , law "cutCall empty  =  empty" $
      equal g run (cutCall empty) empty
  , law "cutCall (return x <|> m)  =  return x <|> cutCall m" $ do
      x <- forAll genInt
      m <- forAllM g
      equal g run (cutCall (return x <|> m)) (return x <|> cutCall m)
  , law "cutCall (cut >> m)  =  cutCall m" $ do
      m <- forAllM g
      equal g run (cutCall (cut >> m)) (cutCall m)
  , law "cutCall (cutCall m)  =  cutCall m" $ do
      m <- forAllM g
      equal g run (cutCall (cutCall m)) (cutCall m)
  ]

onceLaws :: (Members '[Empty, Choose, Once] effs, Eq b, Show b)
         => GenProg effs -> Run effs b -> [TestTree]
onceLaws g run =
  [ law "once empty  =  empty" $
      equal g run (once empty) empty
  , law "once (return x <|> m)  =  return x" $ do
      x <- forAll genInt
      m <- forAllM g
      equal g run (once (return x <|> m)) (return x)
  , law "once (once m)  =  once m" $ do
      m <- forAllM g
      equal g run (once (once m)) (once m)
  ]

examples :: TestTree
examples = testGroup "examples"
  [ testCase "knapsack, list" $
      handle list (knapsack 3 [3, 2, 1]) @?= [[3],[2,1],[1,2],[1,1,1]]

    -- `list'` is not a modular handler and uses `eval` directly
  , testCase "knapsack, list'" $
      list' (knapsack 3 [3, 2, 1]) @?= [[3],[2,1],[1,2],[1,1,1]]

    -- `nondet` is a modular handler but does not handle `once`. Here it is
    -- immaterial because `once` does not appear in the program,
    -- however it requires `choose` to be algebraic.
  , testCase "knapsack, chooseByNondet |> nondet" $
      handle (chooseByNondet |> List.nondet) (knapsack 3 [3, 2, 1]) @?= [[3],[2,1],[1,2],[1,1,1]]

    -- `backtrack` is modular, and is furthermore simply
    -- the joining of the nondet algebra with an algebra
    -- for once
  , testCase "knapsack, backtrack" $
      handle List.backtrack (knapsack 3 [3, 2, 1]) @?= [[3],[2,1],[1,2],[1,1,1]]

  , testCase "once, backtrack" $
      handle List.backtrack onceExample @?= [1, 2]

  , testCase "once, onceNondet" $
      handle onceNondet onceExample @?= [1, 2]

  , testCase "queens" $
      length (handle list (queens 8)) @?= 92
  ]

knapsack
  :: Int -> [Int] -> [Int] ! [Empty, Choose]
knapsack w vs
  | w <  0    = empty
  | w == 0    = return []
  | otherwise = do v <- select vs
                   vs' <- knapsack (w - v) vs
                   return (v : vs')

-- | `list` evaluates a nondeterministic computation and collects all results
-- into a list. It handles the t`Empty`, t`Choose`, and t`Once` effects.
list' :: Prog [Empty, Choose, Once] a -> [a]
list' = eval halg where
  halg :: Algebra [Empty, Choose, Once] []
  halg = (\Empty -> []) :#
         (\(Choose xs ys) -> xs ++ ys) :#.
         (\(Once xs) -> case xs of [] -> []; (x:_) -> [x])

onceExample :: Int ! [Empty, Choose, Once]
onceExample = do x <- once (return 0 <|> return 5)
                 return (x + 1) <|> return (x + 2)

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
    noThreat []      _ _  = True
    noThreat (q:qs)  c r  = abs (q - c) /= r && noThreat qs c (r+1)
