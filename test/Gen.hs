{-# LANGUAGE DataKinds #-}
{-|
Module      : Gen
Description : Generators of programs
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

Generators of programs.
-}
module Gen
  ( GenProg (..)
    -- * Generators
  , genInt, genInts
  , genAlg
  , genProg, genOperation
    -- * Quantification
  , forAllM, forAllK, forAllK2
  ) where

import Control.Effect

import Hedgehog (Gen, PropertyT, forAllWith)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

newtype GenProg effs = GenProg
  (forall env. Gen (env -> Prog effs Int) -> [Gen (env -> Prog effs Int)])

instance Semigroup (GenProg effs) where
  GenProg f <> GenProg g = GenProg (\sub -> f sub ++ g sub)

instance Monoid (GenProg effs) where
  mempty = GenProg (const [])

genInt :: Gen Int
genInt = Gen.int (Range.linearFrom 0 (-100) 100)

genInts :: Gen [Int]
genInts = Gen.list (Range.linear 0 4) genInt

genAlg :: [Int -> Prog effs Int] -> GenProg effs
genAlg ops = GenProg $ \sub ->
  [ Gen.subterm sub (\p env -> p env >>= op) | op <- ops ]

-- | Programs built from the given operations, @return@ and sequencing, with
-- the given variables in scope.
genOpen :: [env -> Int] -> GenProg effs -> Gen (env -> Prog effs Int)
genOpen vars (GenProg ops) = Gen.sized $ \n ->
  let sub | n <= 1    = leaf
          | otherwise = Gen.small (genOpen vars (GenProg ops))
  in Gen.choice (leaf : Gen.subterm2 sub sub seqPlus : ops sub)
  where
    leaf = (\a env -> return (a env)) <$> Gen.choice ((const <$> genInt) : map pure vars)
    seqPlus p q env = (+) <$> p env <*> q env

genProg :: GenProg effs -> Gen (Prog effs Int)
genProg ops = ($ ()) <$> genOpen [] ops

genOperation :: GenProg effs -> Gen (Prog effs Int)
genOperation (GenProg ops) = ($ ()) <$> Gen.choice (ops (const . return <$> genInt))

forAllM :: Monad m => GenProg effs -> PropertyT m (Prog effs Int)
forAllM = forAllWith (const "<program>") . genProg

forAllK :: Monad m => GenProg effs -> PropertyT m (Int -> Prog effs Int)
forAllK = forAllWith (const "<continuation>") . genOpen [id]

forAllK2 :: Monad m => GenProg effs -> PropertyT m (Int -> Int -> Prog effs Int)
forAllK2 = forAllWith (const "<continuation>") . fmap curry . genOpen [fst, snd]
