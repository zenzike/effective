{-# LANGUAGE DataKinds #-}

{-|
Module      : Effect.Writer
Description : Laws for writers and censoring
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}
module Effect.Writer (tests, theory, censorTheory, laws, censorLaws, genWriter, genCensor) where

import Control.Effect
import Control.Effect.Writer


import Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import Law
import Gen

tests :: TestTree
tests = testGroup "Writer"
  [ testGroup "laws"
    [ testGroup "writer"              $ laws genWriter (\_ -> handle (writer @[Int]))
    , testGroup "censors f |> writer" $ laws (genWriter <> genCensor) censored ++ censorLaws (genWriter <> genCensor) censored
    ]
  , testGroup "handlers"
    [ law "writer_ discards the output" $
        agree (genWriter @'[Tell [Int]]) (\_ -> handle (writer_ @[Int])) (\_ -> snd . handle (writer @[Int]))
    , law "censors id  =  uncensors" $
        agree (genWriter @'[Tell [Int]]) (\_ -> censored 0) (\_ -> handle (uncensors @[Int] |> writer @[Int]))
    , law "the initial censor applies to all output" $
        agree (genWriter @'[Tell [Int]])
          censored
          (\n p -> let (w, x) = censored 0 p in (map (+ n) w, x))
    ]
  ]
  where
    censored :: Run '[Tell [Int], Censor [Int]] ([Int], Int)
    censored n = handle (censors @[Int] (map (+ n)) |> writer @[Int])

genWriter :: Member (Tell [Int]) effs => GenProg effs
genWriter = genAlg [\x -> x <$ tell [x]]

theory :: (Member (Tell [Int]) effs, Eq b, Show b) => Theory effs b
theory = Theory "writer" genWriter laws

censorTheory :: (Members '[Tell [Int], Censor [Int]] effs, Eq b, Show b) => Theory effs b
censorTheory = Theory "writer with censor" (genWriter <> genCensor) (\g run -> laws g run ++ censorLaws g run)

genCensor :: Member (Censor [Int]) effs => GenProg effs
genCensor = GenProg $ \sub ->
  [ Gen.subtermM sub (\p -> (\n env -> censor @[Int] (map (+ n)) (p env)) <$> genInt) ]

laws :: (Member (Tell [Int]) effs, Eq b, Show b)
     => GenProg effs -> Run effs b -> [TestTree]
laws g run =
  [ law "tell mempty  =  return ()" $
      equal_ g run (tell @[Int] []) (return ())
  , law "tell v >> tell w  =  tell (v <> w)" $ do
      v <- forAll genInts
      w <- forAll genInts
      equal_ g run (tell v >> tell w) (tell (v <> w))
  ]

censorLaws :: (Members '[Tell [Int], Censor [Int]] effs, Eq b, Show b)
           => GenProg effs -> Run effs b -> [TestTree]
censorLaws g run =
  [ law "censor f (tell w)  =  tell (f w)" $ do
      w <- forAll genInts
      equal_ g run (censor @[Int] (map (+ 1)) (tell w)) (tell (map (+ 1) w))
  , law "censor f (return x)  =  return x" $ do
      x <- forAll genInt
      equal g run (censor @[Int] reverse (return x)) (return x)
  , law "censor f (m >>= k)  =  censor f m >>= censor f . k" $ do
      m <- forAllM g
      k <- forAllK g
      equal g run
        (censor @[Int] (map (+ 1)) (m >>= k))
        (censor @[Int] (map (+ 1)) m >>= censor @[Int] (map (+ 1)) . k)
  , law "censor f . censor g  =  censor (f . g)" $ do
      m <- forAllM g
      equal g run
        (censor @[Int] (map (+ 1)) (censor @[Int] (map (* 2)) m))
        (censor @[Int] (map (+ 1) . map (* 2)) m)
  ]
