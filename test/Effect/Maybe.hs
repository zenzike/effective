{-# LANGUAGE DataKinds #-}

{-|
Module      : Effect.Maybe
Description : Laws and examples for exceptions that carry no value
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}
module Effect.Maybe
  ( tests, theory, retryTheory, laws, retryLaws, genThrow, genExcept ) where

import Control.Effect
import Control.Effect.Maybe
import Control.Effect.State

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

import Law
import Gen

tests :: TestTree
tests = testGroup "Maybe"
  [ testGroup "laws"
    [ testGroup "except" $ laws genExcept (\_ -> handle except)
    , testGroup "retry"  $ retryLaws genThrow (\_ -> handle retry)
    ]
  , examples
  ]

theory :: (Members '[Throw, Catch] effs, Eq b, Show b) => Theory effs b
theory = Theory "exceptions" genExcept laws

retryTheory :: (Members '[Throw, Catch] effs, Eq b, Show b) => Theory effs b
retryTheory = Theory "exceptions" genThrow retryLaws

genThrow :: Member Throw effs => GenProg effs
genThrow = genAlg [const throw]

genExcept :: Members '[Throw, Catch] effs => GenProg effs
genExcept = genThrow <> GenProg (\sub -> [ Gen.subterm2 sub sub (\p q env -> catch (p env) (q env)) ])

laws :: (Members '[Throw, Catch] effs, Eq b, Show b)
     => GenProg effs -> Run effs b -> [TestTree]
laws g run =
  [ law "throw >>= k  =  throw" $ do
      k <- forAllK g
      equal g run (throw >>= k) throw
  , law "catch throw h  =  h" $ do
      h <- forAllM g
      equal g run (catch throw h) h
  , law "catch (return x) h  =  return x" $ do
      x <- forAll genInt
      h <- forAllM g
      equal g run (catch (return x) h) (return x)
  , law "catch m throw  =  m" $ do
      m <- forAllM g
      equal g run (catch m throw) m
  , law "catch (catch m h) h'  =  catch m (catch h h')" $ do
      m  <- forAllM g
      h  <- forAllM g
      h' <- forAllM g
      equal g run (catch (catch m h) h') (catch m (catch h h'))
  ]

retryLaws :: (Members '[Throw, Catch] effs, Eq b, Show b)
          => GenProg effs -> Run effs b -> [TestTree]
retryLaws g run =
  [ law "throw >>= k  =  throw" $ do
      k <- forAllK g
      equal g run (throw >>= k) throw
  , law "catch (return x) h  =  return x" $ do
      x <- forAll genInt
      h <- forAllM g
      equal g run (catch (return x) h) (return x)
  , law "catch m throw  =  m" $ do
      m <- forAllM g
      equal g run (catch m throw) m
  ]

examples :: TestTree
examples = testGroup "examples"
  [ testProperty "monus" $ property $ do
      x <- forAll $ Gen.int $ Range.linear 1 1000
      y <- forAll $ Gen.int $ Range.linear 1 1000
      handle except (monus x y) === if x < y then Nothing else Just (x - y)

  , testProperty "safeMonus" $ property $ do
      x <- forAll $ Gen.int $ Range.linear 1 1000
      y <- forAll $ Gen.int $ Range.linear 1 1000
      handle except (safeMonus x y) === if x < y then Just 0 else Just (x - y)

  , testCase "retry gives up when the recovery fails" $
      handle retry (catch throw throw) @?= (Nothing :: Maybe Int)

  , testCase "retry does not run the recovery of a success" $
      handle retry (catch (return 1) throw) @?= Just (1 :: Int)

  , testProperty "retry runs the body again when the recovery succeeds" $ property $ do
      n <- forAll $ Gen.int $ Range.linear 0 100
      handle (retry  |> state n) (catch flaky (return 0)) === (Just 0, 0)
      handle (except |> state n) (catch flaky (return 0)) === (Just 0, max 0 (n - 1))
  ]

monus :: Int -> Int -> Int ! '[Throw]
monus x y = do if x < y then throw else return (x - y)

safeMonus :: Int -> Int -> Prog '[Throw, Catch] Int
safeMonus x y = catch (monus x y) (return 0)

flaky :: Members '[Get Int, Put Int, Throw] effs => Prog effs Int
flaky = do n <- get
           if n > 0 then do put (n - 1); throw else return n
