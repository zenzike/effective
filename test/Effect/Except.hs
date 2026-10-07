{-# LANGUAGE DataKinds #-}

{-|
Module      : Effect.Except
Description : Laws for exceptions that carry a value
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}
module Effect.Except
  ( tests, theory, retryTheory
  , laws, retryLaws
  , genThrow, genExcept
  ) where

import Control.Effect
import Control.Effect.Except

import Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import Law
import Gen

tests :: TestTree
tests = testGroup "Except"
  [ testGroup "laws"
    [ testGroup "except" $ laws genExcept (\_ -> handle (except @Int))
    , testGroup "retry"  $ retryLaws genThrow (\_ -> handle (retry @Int))
    ]
  ]

theory :: (Members '[Throw Int, Catch Int] effs, Eq b, Show b) => Theory effs b
theory = Theory "exceptions" genExcept laws

retryTheory :: (Members '[Throw Int, Catch Int] effs, Eq b, Show b) => Theory effs b
retryTheory = Theory "exceptions" genThrow retryLaws

genThrow :: Member (Throw Int) effs => GenProg effs
genThrow = genAlg [throw]

genExcept :: Members '[Throw Int, Catch Int] effs => GenProg effs
genExcept = genThrow <> GenProg (\sub ->
  [ Gen.subterm2 sub sub (\p q env -> catch (p env) (\e -> (e +) <$> q env)) ])

laws :: (Members '[Throw Int, Catch Int] effs, Eq b, Show b)
     => GenProg effs -> Run effs b -> [TestTree]
laws g run =
  [ law "throw e >>= k  =  throw e" $ do
      e <- forAll genInt
      k <- forAllK g
      equal g run (throw e >>= k) (throw e)
  , law "catch (throw e) h  =  h e" $ do
      e <- forAll genInt
      h <- forAllK g
      equal g run (catch (throw e) h) (h e)
  , law "catch (return x) h  =  return x" $ do
      x <- forAll genInt
      h <- forAllK g
      equal g run (catch (return x) h) (return x)
  , law "catch m throw  =  m" $ do
      m <- forAllM g
      equal g run (catch @Int m throw) m
  , law "catch (catch m h) h'  =  catch m (\\e -> catch (h e) h')" $ do
      m  <- forAllM g
      h  <- forAllK g
      h' <- forAllK g
      equal g run (catch (catch m h) h') (catch m (\e -> catch (h e) h'))
  ]

retryLaws :: (Members '[Throw Int, Catch Int] effs, Eq b, Show b)
          => GenProg effs -> Run effs b -> [TestTree]
retryLaws g run =
  [ law "throw e >>= k  =  throw e" $ do
      e <- forAll genInt
      k <- forAllK g
      equal g run (throw e >>= k) (throw e)
  , law "catch (return x) h  =  return x" $ do
      x <- forAll genInt
      h <- forAllK g
      equal g run (catch (return x) h) (return x)
  , law "catch m throw  =  m" $ do
      m <- forAllM g
      equal g run (catch @Int m throw) m
  ]
