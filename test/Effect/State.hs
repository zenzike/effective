{-# LANGUAGE DataKinds #-}

{-|
Module      : Effect.State
Description : Laws and examples for state
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}
module Effect.State (tests, theory, laws, genState) where

import Control.Effect
import Control.Effect.State
import qualified Control.Effect.State.Lazy as Lazy
import Control.Effect.Maybe
import Control.Effect.Reader
import Control.Monad (replicateM_)

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

import Law
import Gen

tests :: TestTree
tests = testGroup "State"
  [ testGroup "laws"
    [ testGroup "state"            $ laws genState (\s -> handle (state s))
    , testGroup "state_"           $ laws genState (\s -> handle (state_ s))
    , testGroup "Lazy.state"       $ laws genState (\s -> handle (Lazy.state s))
    , testGroup "Lazy.state_"      $ laws genState (\s -> handle (Lazy.state_ s))
    ]
  , testGroup "handlers"
    [ law "state and Lazy.state agree" $
        agree (genState @'[Get Int, Put Int]) (\s -> handle (state s)) (\s -> handle (Lazy.state s))
    , law "Lazy.state_ discards the final state" $
        agree (genState @'[Get Int, Put Int]) (\s -> handle (Lazy.state_ s)) (\s -> fst . handle (Lazy.state s))
    , law "state_ discards the final state" $
        agree (genState @'[Get Int, Put Int]) (\s -> handle (state_ s)) (\s -> fst . handle (state s))
    ]
  , examples
  ]

genState :: Members '[Get Int, Put Int] effs => GenProg effs
genState = genAlg [const get, \s -> s <$ put s]

theory :: (Members '[Get Int, Put Int] effs, Eq b, Show b) => Theory effs b
theory = Theory "state" genState laws

laws :: (Members '[Get Int, Put Int] effs, Eq b, Show b)
     => GenProg effs -> Run effs b -> [TestTree]
laws g run =
  [ law "put s >> get  =  put s >> return s" $ do
      s <- forAll genInt
      equal g run (put s >> get) (put s >> return s)
  , law "put s >> put s'  =  put s'" $ do
      s  <- forAll genInt
      s' <- forAll genInt
      equal_ g run (put s >> put s') (put s')
  , law "get >>= \\s -> get >>= \\s' k s s'  =  get >>= \\s -> k s s" $ do
      k <- forAllK2 g
      equal g run (get >>= \s -> get >>= \s' -> k s s') (get >>= \s -> k s s)
  , law "get >>= put  =  return ()" $
      equal_ g run (get >>= put @Int) (return ())
  ]

examples :: TestTree
examples = testGroup "examples"
  [ testProperty "incr" $ property $ do
      n <- forAll $ Gen.int $ Range.linear 1 1000
      handle (state n) incr === ((), n + 1)

  , testProperty "decr, local state" $ property $ do
      n <- forAll $ Gen.int $ Range.linear (-1000) 1000
      handle (localState n) decr === if n > 0 then Just ((), n - 1) else Nothing

  , testProperty "decr, global state" $ property $ do
      n <- forAll $ Gen.int $ Range.linear (-1000) 1000
      handle (globalState n) decr === if n > 0 then (Just (), n - 1) else (Nothing, n)

  , testProperty "incr >> decr, local state" $ property $ do
      n <- forAll $ Gen.int $ Range.linear (-1000) 1000
      handle (localState n) (do incr; decr) === if n >= 0 then Just ((), n) else Nothing

  , testProperty "incr >> decr, global state" $ property $ do
      n <- forAll $ Gen.int $ Range.linear (-1000) 1000
      handle (globalState n) (do incr; decr) === if n >= 0 then (Just (), n) else (Nothing, n + 1)

    -- This is global state because the `Int` is decremented
    -- twice before the exception is thrown.
  , testCase "catchDecr, global state" $
      handle (globalState 2) catchDecr @?= (Just (), 0 :: Int)

    -- With local state, the state is reset to its value
    -- before the catch where the exception was raised.
  , testCase "catchDecr, local state" $
      handle (localState 2) catchDecr @?= Just ((), 1 :: Int)

    -- For instance you might want to allocate a bit more memory ...
    -- and a bit more ... and so on.
  , testCase "retry" $
      handle (retry |> state 2) catchDecr44 @?= (Just (), 42 :: Int)

  , testCase "get by ask" $
      handle (getToAsk |> reader (0 :: Int)) getAsk @?= (100, 100)

  , testCase "get by ask, below another reader" $
      handle (reader (0 :: Int) |> getToAsk |> reader (200 :: Int)) getAsk @?= (200, 100)
  ]

globalState :: s -> Handler '[Throw, Catch, Put s, Get s] '[] '[MaybeT, StateT s] a (Maybe a, s)
globalState s = except |> state s

localState :: s -> Handler '[Put s, Get s, Throw, Catch] '[] '[StateT s, MaybeT] a (Maybe (a, s))
localState s = state s |> except

incr :: () ! [Get Int, Put Int]
incr = do
  x <- get
  put @Int (x + 1)

decr :: () ! [Get Int, Put Int, Throw]
decr = do
  x <- get
  if x > 0
    then put @Int (x - 1)
    else throw

catchDecr :: () ! [Get Int, Put Int, Throw, Catch]
catchDecr = do
  decr
  catch
    (do decr
        decr)
    (return ())

catchDecr44 :: () ! [Get Int, Put Int, Throw, Catch]
catchDecr44 = do
  decr
  catch
    (do decr
        decr)
    (do replicateM_ 44 incr)

getAsk :: (Int, Int) ! [Get Int, Local Int, Ask Int]
getAsk = local (+ (100 :: Int)) (do x <- get ; y <- ask ; return (x , y) )

getToAsk :: Handler '[Get Int] '[Ask Int] '[] a a
getToAsk = interpret1 $
    \(Get k) -> do y <- ask @Int
                   return (k y)
