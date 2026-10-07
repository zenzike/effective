{-# LANGUAGE AllowAmbiguousTypes, MonoLocalBinds, CPP #-}
{-|
Module      : Effect.HStore
Description : Tests of the higher-order store
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental
-}
module Effect.HStore (tests) where

import Prelude hiding (or)
import Control.Exception (SomeException, try, evaluate)
import Control.Effect
import Control.Effect.HStore.Unsafe
import qualified Control.Effect.HStore.Safe as Safe
import qualified Control.Effect.State as St
import Control.Effect.Nondet.List
import Data.List.Kind
import Data.Functor.Identity

import Hedgehog (forAll, (===))
import Test.Tasty
import Test.Tasty.HUnit

import Gen (genInt)
import Law (law)

prog1 :: Int ! '[New, Get, Put]
prog1 = do iRef <- new @Int 1
           fRef <- new @(Int -> Int) (\i -> i * i)
           f <- get fRef
           put iRef 2
           i <- get iRef
           return (f i)

test1 :: Int
test1 = handle hstore prog1

landinKnot :: forall effs. Members '[New, Get, Put] effs => Prog effs Int
landinKnot =
  do fRef <- new (\i -> return 0)
     let factorial :: Int -> Prog effs Int
         factorial 0 = return 1
         factorial n = do f <- get fRef; fmap (n *) (f (n - 1))
     put fRef factorial
     factorial 5

test2 :: Int
test2 = handle hstore landinKnot   -- 120

goWrong :: forall effs. Members '[New, Get, Put] effs => Prog effs Int
goWrong = do iRef <- new @Int 0
             return (handle hstore (get iRef))
test3 :: Int
test3 = handle hstore goWrong      -- crash


goWrong2 :: forall effs.
            Members '[ New, Get, Put,
                       Empty, Choose,
                       St.Put (Maybe (Ref Int)), St.Get (Maybe (Ref Int))
                     ] effs
         => Prog effs Int
goWrong2 = do iRef <- new @Int 0
              (do iRef' <- new @Int 0; St.put (Just iRef'); return 0) <|>
                (do r <- St.get;
                    case r of
                      Just iRefFromOtherWorld -> get iRefFromOtherWorld
                      Nothing -> return 0)

test3' :: [Int]
test3' = handle (hstore |> nondet' |> St.state_ @(Maybe (Ref Int)) Nothing) goWrong2

progS :: forall w effs. (Members '[Safe.Put w, Safe.Get w, Safe.New w] effs)
      => Prog effs Int
progS = do iRef <- Safe.new @Int @w 1
           fRef <- Safe.new @(Int -> Int) @w (\i -> i * i)
           f <- Safe.get fRef
           Safe.put iRef 2
           i <- Safe.get iRef
           return (f i)

test4 :: Int
test4 = runIdentity (Safe.handleHSM @'[] emptyAlg progS') where
  progS' :: forall w. Prog (Safe.HSEffs w) Int
  progS' = progS @w

prog2 :: forall w. Int ! '[Choose, Empty, Safe.Put w, Safe.Get w, Safe.New w]
prog2 = do iRef <- Safe.new @Int @w 1
           (do Safe.put iRef 2; return 0) <|> (do Safe.get iRef)

-- State is local if state gets handled first
-- test5 == [0, 1]
test5 :: [Int]
test5 = handle nondet' (Safe.handleHSP prog2') where
  prog2' :: forall w effs.
         ( Members '[Empty, Choose] effs )
         => Prog (Safe.HSEffs w :++ effs) Int
  prog2' = prog2 @w

-- State is global if state gets handled later
-- test6 == [0, 2]
test6 :: [Int]
test6 = Safe.runHS (handleP nondet' (prog2 @w)
                      :: forall w. Prog (Safe.HSEffs w) [Int])

safeNewGet :: forall w. Int -> Prog (Safe.HSEffs w) Int
safeNewGet v = Safe.new @Int @w v >>= Safe.get

safePutGet :: forall w. Int -> Int -> Prog (Safe.HSEffs w) Int
safePutGet v x = do r <- Safe.new @Int @w v; Safe.put r x; Safe.get r

safeIndependent :: forall w. Int -> Int -> Int -> Prog (Safe.HSEffs w) Int
safeIndependent v u x =
  do r <- Safe.new @Int @w v; r' <- Safe.new @Int @w u; Safe.put r' x; Safe.get r

crashes :: Int -> Assertion
crashes x = do
  r <- try (evaluate x)
  case r of
    Left (_ :: SomeException) -> return ()
    Right v -> assertFailure ("no crash, result " ++ show v)

tests :: TestTree
tests = testGroup "HStore"
  [ testGroup "Unsafe"
    [ law "new v >>= get  =  return v" $ do
        v <- forAll genInt
        handle hstore (new v >>= get) === v
    , law "put r w >> get r  =  put r w >> return w" $ do
        v <- forAll genInt
        w <- forAll genInt
        handle hstore (new v >>= \r -> put r w >> get r) === w
    , law "references are independent" $ do
        v <- forAll genInt
        w <- forAll genInt
        x <- forAll genInt
        handle hstore (do r <- new v; r' <- new w; put r' x; get r) === v
    , testCase "references of different types" $ test1 @?= 4
    , testCase "Landin's knot"                 $ test2 @?= 120
    , testCase "a reference used under another handle crashes" $ crashes test3
    , testCase "a reference from another branch crashes"       $ crashes (sum test3')
    ]
  , testGroup "Safe"
    [ law "new v >>= get  =  return v" $ do
        v <- forAll genInt
        Safe.runHS (safeNewGet v) === v
    , law "put r w >> get r  =  put r w >> return w" $ do
        v <- forAll genInt
        w <- forAll genInt
        Safe.runHS (safePutGet v w) === w
    , law "references are independent" $ do
        v <- forAll genInt
        w <- forAll genInt
        x <- forAll genInt
        Safe.runHS (safeIndependent v w x) === v
    , testCase "references of different types" $ test4 @?= 4
    , testCase "state is local if handled before nondeterminism" $ test5 @?= [0, 1]
    , testCase "state is global if handled after nondeterminism" $ test6 @?= [0, 2]
    ]
  ]
