{-|
Module      : Control.Effect.Concurrency
Description : The effect of concurrency with communication.
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides the operations and handlers for concurrency synchronised
communications (in the style of process calculi). There are currently two kinds
of handlers:

  1. resumption-based handlers that are useful for exploring all the possible
     behaviours of a concurrent system, and

  2. native-IO-based handlers that are useful for actually running a concurrent
     process efficiently (using the native concurrency API from
     "Control.Concurrent" of GHC).
-}
module Control.Effect.Concurrency (
  -- * Syntax
  -- | Signatures and operations are in this module.
  module Control.Effect.Concurrency.Type,

  -- * Semantics

  -- ** Resumption-based handlers
  resump,
  resumpWith,
  resumpWithM,
  resumpAT,
  jresumpAT,
  jresump,
  jresumpWith,


  -- ** IO-based handlers
  ccsByQSem,
  parIOAlg,
  jparIOAlg,

  -- ** Re-exported types used by handlers
  Control.Monad.Trans.CRes.ListActs (..),
  Control.Monad.Trans.CRes.ActsMb (..),
  Control.Monad.Trans.CRes.CResT (..),
  ) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Family.Distributive
import Control.Effect.Concurrency.Type
import Control.Effect.IO (io)
import qualified Control.Effect.Reader as R
import qualified Control.Effect.Except as E
import qualified Control.Monad.Trans.CRes as C

import Control.Concurrent ( forkIO, QSem )
import qualified Control.Concurrent.MVar as MVar
import qualified Control.Concurrent.QSem as QSem
import Control.Monad.Trans.CRes
import qualified Data.Map as M
import Data.HFunctor

-- | Algebra for the resumption-based handler of t`Par`, t`Act`, and t`Res`.
resumpAlg :: (Action a, Monad m) => Algebra '[Act a, Par, Res a] (C.CResT a m)
resumpAlg (Act a p) = prefix a (return p)
resumpAlg (Par l r) = C.par l r
resumpAlg (Res a p) = C.res a p

-- | Algebra for the resumption-based handler of t`JPar`, t`Act`, and t`Res`.
jresumpAlg :: (Action a, Monad m) => Algebra '[Act a, JPar, Res a] (C.CResT a m)
jresumpAlg (Act a p)    = prefix a (return p)
jresumpAlg (JPar l r c) = fmap (\(x, y) -> c (JPar_ x y)) (C.jpar l r)
jresumpAlg (Res a p)    = C.res a p

-- | Algebra transformer for the resumption-based handler of t`Par`, t`Act`, and t`Res`.
resumpAT :: forall a. Action a => AlgTrans '[Act a, Par, Res a] '[] '[C.CResT a] Monad
resumpAT = AlgTrans (\_ -> resumpAlg)

-- | Algebra transformer for the resumption-based handler of t`JPar`, t`Act`, and t`Res`.
jresumpAT :: forall a. Action a => AlgTrans '[Act a, JPar, Res a] '[] '[C.CResT a] Monad
jresumpAT = AlgTrans (\_ -> jresumpAlg)

-- | Resumption-based handler of concurrency. Non-deterministic branches are explored
-- by backtracking, resulting in a list of all (successful) traces.
resump :: forall a b . Action a => Handler '[Act a, Par, Res a] '[] '[C.CResT a] b (C.ListActs a b)
resump = handler' runAll (\_ -> resumpAlg)

-- | Resumption-based handler of concurrency. Non-deterministic choices are resolved
-- with the given list Booleans.
resumpWith :: forall a b . Action a => [Bool] -> Handler '[Act a, Par, Res a] '[] '[C.CResT a] b (ActsMb a b)
resumpWith choices = handler' (runWith choices) (\_ -> resumpAlg)

-- | Resumption-based handler of concurrency. Non-deterministic choices are resolved
-- with the given program (of effect @sig@).
resumpWithM :: forall sig a b .
               ( HFunctor (Effs sig) , Action a )
            => Prog sig Bool -> Handler '[Act a, Par, Res a] sig '[C.CResT a] b (ActsMb a b)
resumpWithM pb = handler (\oalg -> runWithM (eval oalg pb))  (\_ -> resumpAlg)

-- | Resumption-based handler of concurrency with joined parallel composition.
-- Non-deterministic branches are explored by backtracking, resulting in a list
-- of all (successful) traces.
jresump :: forall a b . Action a => Handler '[Act a, JPar, Res a] '[] '[C.CResT a] b (C.ListActs a b)
jresump = handler' runAll (\_ -> jresumpAlg)

-- | Resumption-based handler of concurrency with joined parallel composition.
-- Non-deterministic choices are resolved with the given list Booleans.
jresumpWith :: forall a b. Action a => [Bool] -> Handler '[Act a, JPar, Res a] '[] '[C.CResT a] b (ActsMb a b)
jresumpWith choices = handler' (runWith choices) (\_ -> jresumpAlg)

-- | Resumption-based handler of concurrency with joined parallel composition.
-- Non-deterministic choices are resolved with the given program (of effect @sig@).
jresumpWithM :: forall sig a b.
                ( HFunctor (Effs sig) , Action a )
             => Prog sig Bool -> Handler '[Act a, JPar, Res a] sig '[C.CResT a] b (ActsMb a b)
jresumpWithM pb = handler (\oalg -> runWithM (eval oalg pb)) (\_ -> jresumpAlg)

type QSemMap a = M.Map a (QSem, QSem)

-- | IO-based handler of concurrency. The effect of restriction is translated
-- to creating new semaphores, and performing (synchronised) actions is translated
-- to operations on semaphores.
-- Note that operations t`Par` and t`JPar` are part of the IO-effects in "Control.Effect.IO",
-- so they don't need to be handled here.
ccsByQSem :: forall n a . Ord n
          => Handler '[Act (CCSAction n), Res (CCSAction n)]
                     '[Alg IO]
                     '[R.ReaderT (QSemMap n), E.ExceptT String]
                     a
                     (Either String a)
ccsByQSem = (interpretM alg ||> R.reader M.empty) ||> E.except where
  alg :: Monad m => Algebra '[ R.Ask (QSemMap n), R.Local (QSemMap n)
                             , E.Throw String, Alg IO
                             ] m
                 -> Algebra '[Act (CCSAction n), Res (CCSAction n)] m
  alg oalg (Act (Action n) p) = eval oalg $ do
    m <- R.ask @(QSemMap n)
    case M.lookup n m of
      Just (s1, s2) -> do io (QSem.waitQSem s1); io (QSem.signalQSem s2)
      Nothing  -> E.throw "Channel used before creation!"
    return p
  alg oalg (Act (CoAction n) p) = eval oalg $ do
    m <- R.ask @(QSemMap n)
    case M.lookup n m of
      Just (s1, s2) -> do io (QSem.signalQSem s1); io (QSem.waitQSem s2)
      Nothing  -> E.throw "Channel used before creation!"
    return p
  alg oalg (Res a p) = do
    (m, s1, s2) <- eval oalg $ do
       m <- R.ask @(QSemMap n)
       s1 <- io (QSem.newQSem 0)
       s2 <- io (QSem.newQSem 0)
       return (m, s1, s2)
    let m' = M.insert (getActionName a) (s1, s2) m
    R.localM oalg (const m') p

-- | Interprets t`Control.Effect.Concurrency.Par` using the native concurrency API.
-- from `Control.Concurrent`.
parIOAlg :: Algebra '[Par] IO
parIOAlg (Par l r) = Control.Concurrent.forkIO (fmap (const ()) r) >> l

-- | Interprets t`Control.Effect.Concurrency.JPar` using the native concurrency API.
-- from "Control.Concurrent". The result from the child thread is passed back to the
-- main thread using @MVar@.
jparIOAlg :: Algebra '[JPar] IO
jparIOAlg (JPar l r c) = do
  m <- MVar.newEmptyMVar
  Control.Concurrent.forkIO $
    do y <- r; MVar.putMVar m y
  x <- l
  y' <- MVar.takeMVar m
  return (c (JPar_ x y'))