{-# LANGUAGE DataKinds #-}

{-|
Module      : Effect.Reader
Description : Laws for readers
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}
module Effect.Reader (tests, theory, askLaws, laws, genAsk, genReader) where

import Control.Effect
import Control.Effect.Reader


import Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import Law
import Gen

tests :: TestTree
tests = testGroup "Reader"
  [ testGroup "laws"
    [ testGroup "reader"           $ laws genReader (\r -> handle (reader r))
    , testGroup "asker"            $ askLaws genAsk (\r -> handle (asker r))
    ]
  , testGroup "handlers"
    [ law "reader and asker agree" $
        agree (genAsk @'[Ask Int]) (\r -> handle (reader r)) (\r -> handle (asker r))
    ]
  ]

genAsk :: Member (Ask Int) effs => GenProg effs
genAsk = genAlg [const ask]

theory :: (Members '[Ask Int, Local Int] effs, Eq b, Show b) => Theory effs b
theory = Theory "reader" genReader laws

genReader :: Members '[Ask Int, Local Int] effs => GenProg effs
genReader = genAsk <> GenProg (\sub ->
  [ Gen.subtermM sub (\p -> (\n env -> local (+ n) (p env)) <$> genInt) ])

askLaws :: (Member (Ask Int) effs, Eq b, Show b)
        => GenProg effs -> Run effs b -> [TestTree]
askLaws g run =
  [ law "ask >> return ()  =  return ()" $
      equal_ g run (() <$ ask @Int) (return ())
  , law "ask >>= \\r -> ask >>= k r  =  ask >>= \\r -> k r r" $ do
      k <- forAllK2 g
      equal g run (ask >>= \r -> ask >>= \r' -> k r r') (ask >>= \r -> k r r)
  ]

laws :: (Members '[Ask Int, Local Int] effs, Eq b, Show b)
     => GenProg effs -> Run effs b -> [TestTree]
laws g run = askLaws g run ++
  [ law "local f ask  =  fmap f ask" $ do
      n <- forAll genInt
      equal g run (local (+ n) ask) (fmap (+ n) ask)
  , law "local f (return x)  =  return x" $ do
      n <- forAll genInt
      x <- forAll genInt
      equal g run (local (+ n) (return x)) (return x)
  , law "local f (m >>= k)  =  local f m >>= local f . k" $ do
      n <- forAll genInt
      m <- forAllM g
      k <- forAllK g
      equal g run (local (+ n) (m >>= k)) (local (+ n) m >>= local (+ n) . k)
  , law "local f . local g  =  local (g . f)" $ do
      n <- forAll genInt
      m <- forAllM g
      equal g run (local (+ n) (local @Int (* 2) m)) (local @Int ((* 2) . (+ n)) m)
  ]
