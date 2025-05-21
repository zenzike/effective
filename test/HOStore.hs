{-# LANGUAGE AllowAmbiguousTypes, MonoLocalBinds, CPP #-}
module Main where

import Prelude hiding (or)
import Control.Effect
import Control.Effect.HOStore.Unsafe
import qualified Control.Effect.HOStore.Safe as Safe
import qualified Control.Effect.State as St
import Control.Effect.Nondet
import Data.List.Kind
import Data.Functor.Identity
import Data.HFunctor

prog1 :: Progs '[New, Get, Put] Int
prog1 = do iRef <- new @Int 1
           fRef <- new @(Int -> Int) (\i -> i * i)
           f <- get fRef
           put iRef 2
           i <- get iRef
           return (f i)

test1 :: Int
test1 = handle hstore prog1

landinKnot :: forall sig. Members '[New, Get, Put] sig => Prog sig Int
landinKnot =
  do fRef <- new (\i -> return 0)
     let factorial :: Int -> Prog sig Int
         factorial 0 = return 1
         factorial n = do f <- get fRef; fmap (n *) (f (n - 1))
     put fRef factorial
     factorial 5

test2 :: Int
test2 = handle hstore landinKnot   -- 120

goWrong :: forall sig. Members '[New, Get, Put] sig => Prog sig Int
goWrong = do iRef <- new @Int 0
             return (handle hstore (get iRef))
test3 = handle hstore goWrong      -- crash


goWrong2 :: forall sig. 
            Members '[ New, Get, Put, 
                       Choose, 
                       St.Put (Maybe (Ref Int)), St.Get (Maybe (Ref Int))
                     ] sig
         => Prog sig Int
goWrong2 = do iRef <- new @Int 0
              or (do iRef' <- new @Int 0; St.put (Just iRef'); return 0)
                 (do r <- St.get;
                     case r of 
                       Just iRefFromOtherWorld -> get iRefFromOtherWorld
                       Nothing -> return 0)

test3' :: [Int]
test3' = handle (hstore |> nondet |> St.state_ @(Maybe (Ref Int)) Nothing) goWrong2

progS :: forall w sig. (Members '[Safe.Put w, Safe.Get w, Safe.New w] sig) 
      => Prog sig Int
progS = do iRef <- Safe.new @Int @w 1
           fRef <- Safe.new @(Int -> Int) @w (\i -> i * i)
           f <- Safe.get fRef
           Safe.put iRef 2
           i <- Safe.get iRef
           return (f i)

test4 :: Int
test4 = runIdentity (Safe.handleHSM @'[] absurdEffs progS') where
  progS' :: forall w. Prog (Safe.HSEffs w) Int
  progS' = progS @w

prog2 :: forall w. Progs '[Choose, Empty, Safe.Put w, Safe.Get w, Safe.New w] Int  
prog2 = do iRef <- Safe.new @Int @w 1
           or (do Safe.put iRef 2; return 0) 
              (do Safe.get iRef)

-- State is local if state gets handled first
-- test5 == [0, 1]
test5 :: [Int]
test5 = handle nondet (Safe.handleHSP prog2') where
  prog2' :: forall w sig. 
         ( Members '[Empty, Choose] sig, Append (Safe.HSEffs ()) sig )
         => Prog (Safe.HSEffs w :++ sig) Int
  prog2' = prog2 @w

-- State is global if state gets handled later
-- test6 == [0, 2]
test6 :: [Int]
test6 = Safe.runHS (handleP nondet (prog2 @w) 
                      :: forall w. Prog (Safe.HSEffs w) [Int])

main :: IO ()
main = return ()