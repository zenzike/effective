{-|
Module      : Law
Description : Testing the equations of effect theories
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}
module Law
  ( Run
  , law
  , equal, equal_
  , agree
  , Theory (..)
  , sum
  , commute
  , distribute
  ) where

import Prelude hiding (sum)

import Control.Effect

import Hedgehog
import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Gen

-- | A way of running programs, usually @\\s -> handle (h s)@. The `Int` seeds
-- whatever the handler needs to start from, such as a state or an environment.
type Run effs b = Int -> Prog effs Int -> b

law :: TestName -> PropertyT IO () -> TestTree
law name = testProperty name . property

-- | @equal ops run lhs rhs@ tests @lhs >>= k = rhs >>= k@ for an arbitrary
-- continuation @k@ built from @ops@.
equal :: (Eq b, Show b)
      => GenProg effs -> Run effs b
      -> Prog effs Int -> Prog effs Int -> PropertyT IO ()
equal ops run lhs rhs = do
  s <- forAll genInt
  k <- forAllK ops
  run s (lhs >>= k) === run s (rhs >>= k)

-- | A variant of `equal` for programs with no result.
equal_ :: (Eq b, Show b)
       => GenProg effs -> Run effs b
       -> Prog effs () -> Prog effs () -> PropertyT IO ()
equal_ ops run lhs rhs = equal ops run (0 <$ lhs) (0 <$ rhs)

-- | Two ways of running programs agree on every program built from @ops@.
-- The handlers may each handle more than the effects of @ops@.
agree :: (Members effs effs1, Members effs effs2, Eq b, Show b)
      => GenProg effs -> Run effs1 b -> Run effs2 b -> PropertyT IO ()
agree ops run run' = do
  s <- forAll genInt
  p <- forAllM ops
  run s (weakenProg p) === run' s (weakenProg p)

-- | An effect theory: its name, a generator of its operations, and its laws.
data Theory effs b
  = Theory TestName (GenProg effs) (GenProg effs -> Run effs b -> [TestTree])

-- | The laws of both theories, with the computations they leave free drawn
-- from the sum of the two.
sum :: Theory effs b -> Theory effs b -> Run effs b -> [TestTree]
sum (Theory n1 g1 laws1) (Theory n2 g2 laws2) run =
  [testGroup n1 (laws1 g run), testGroup n2 (laws2 g run)]
  where g = g1 <> g2

-- | Every operation of the one effect commutes with every operation of the
-- other:
--
-- > o1 >>= \a1 -> o2 >>= \a2 -> k a1 a2
-- >   =  o2 >>= \a2 -> o1 >>= \a1 -> k a1 a2
commute :: (Eq b, Show b)
        => GenProg effs -> GenProg effs -> Run effs b -> PropertyT IO ()
commute ops1 ops2 run = do
  o1 <- forAllWith (const "<operation>") (genOperation ops1)
  o2 <- forAllWith (const "<operation>") (genOperation ops2)
  k  <- forAllK2 (ops1 <> ops2)
  s  <- forAll genInt
  run s (o1 >>= \a1 -> o2 >>= \a2 -> k a1 a2)
    === run s (o2 >>= \a2 -> o1 >>= \a1 -> k a1 a2)

-- | The operations of the one effect distribute over those of the other: an
-- operation @o2@ in one position of an operation @o1@ can be moved out of it.
--
-- > o1 >>= \a1 -> if a1 == b then o2 >>= k2 else k1 a1
-- >   =  o2 >>= \a2 -> o1 >>= \a1 -> if a1 == b then k2 a2 else k1 a1
--
-- The position @b@ must be a result that @o1@ can have, so @o1@ is generated
-- together with one, as by `Effect.Nondet.genCoinAt`.
distribute :: (Eq b, Show b)
           => GenProg effs -> Gen (Prog effs Int, Int) -> Gen (Prog effs Int)
           -> Run effs b -> PropertyT IO ()
distribute ops gen1 gen2 run = do
  (o1, b) <- forAllWith (\(_, b) -> "<operation> at " ++ show b) gen1
  o2 <- forAllWith (const "<operation>") gen2
  k1 <- forAllK ops
  k2 <- forAllK ops
  s  <- forAll genInt
  run s (o1 >>= \a1 -> if a1 == b then o2 >>= k2 else k1 a1)
    === run s (o2 >>= \a2 -> o1 >>= \a1 -> if a1 == b then k2 a2 else k1 a1)
