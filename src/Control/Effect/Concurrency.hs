{-|
Module      : Control.Effect.Concurrency
Description : The effect of concurrency with communication.
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides the operations and handlers for concurrency with synchronised
communications (in the style of process calculi). There are currently two kinds
of handlers:

  1. resumption-based handlers, which are useful for exploring all the possible
     behaviours of a concurrent system, and

  2. native-IO-based handlers that are useful for actually running a concurrent
     process efficiently (using the native concurrency API from
     "Control.Concurrent" of GHC).
-}

{-# LANGUAGE LambdaCase #-}
module Control.Effect.Concurrency (
  -- * Syntax
  -- | Signatures and operations are in this module.
  module Control.Effect.Concurrency.Operations,

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
  -- $ioBasedHandler
  ccsByQSem, ccsByQSemC,
  parIOAlg, parIOAlgC,
  jparIOAlg, jparIOAlgC,

  -- ** Re-exported types used by handlers
  Control.Monad.Trans.CRes.ListActs (..),
  Control.Monad.Trans.CRes.ActsMb (..),
  Control.Monad.Trans.CRes.CResT (..),
  QSemMap,
  ) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Family.Distributive
import Control.Effect.Concurrency.Operations
import Control.Effect.IO (io)
import qualified Control.Effect.Reader as R
import qualified Control.Effect.Except as E
import qualified Control.Monad.Trans.CRes as C

import Control.Concurrent ( forkIO, QSem )
import qualified Control.Concurrent.MVar as MVar
import qualified Control.Concurrent.QSem as QSem
import Control.Monad.Trans.CRes
import qualified Data.Map as M

-- * Resumption-based Handlers

-- | Algebra for the resumption-based handler of t`Par`, t`Act`, and t`Res`.
resumpAlg :: (Action a, Monad m) => Algebra '[Act a, Par, Res a] (C.CResT a m)
resumpAlg =
  (\(Act a p) -> prefix a (return p)) :#
  (\(Par l r) -> C.par l r) :#.
  (\(Res a p) -> C.res a p)

-- | Algebra for the resumption-based handler of t`JPar`, t`Act`, and t`Res`.
jresumpAlg :: (Action a, Monad m) => Algebra '[Act a, JPar, Res a] (C.CResT a m)
jresumpAlg =
  (\(Act a p) -> prefix a (return p)) :#
  (\(JPar l r c) -> fmap (\(x, y) -> c (JPar_ x y)) (C.jpar l r)) :#.
  (\(Res a p) -> C.res a p)

-- | Algebra transformer for the resumption-based handler of t`Par`, t`Act`, and t`Res`.
resumpAT :: forall a. Action a => AlgTrans '[Act a, Par, Res a] '[] '[C.CResT a] Monad
resumpAT = AlgTrans (\_ -> resumpAlg)

-- | Algebra transformer for the resumption-based handler of t`JPar`, t`Act`, and t`Res`.
jresumpAT :: forall a. Action a => AlgTrans '[Act a, JPar, Res a] '[] '[C.CResT a] Monad
jresumpAT = AlgTrans (\_ -> jresumpAlg)

-- | Resumption-based handler of concurrency. Non-deterministic branches are explored
-- by backtracking, resulting in a list of all (successful) traces.
resump :: forall a b . Action a => Handler '[Act a, Par, Res a] '[] '[C.CResT a] b (C.ListActs a b)
resump = handler' runAll resumpAlg

-- | Resumption-based handler of concurrency. Non-deterministic choices are resolved
-- with the given list of Booleans.
resumpWith :: forall a b . Action a => [Bool] -> Handler '[Act a, Par, Res a] '[] '[C.CResT a] b (ActsMb a b)
resumpWith choices = handler' (runWith choices) resumpAlg

-- | Resumption-based handler of concurrency. Non-deterministic choices are resolved
-- with the given program (of effect @eff@).
resumpWithM
  :: forall eff a b.
     (Action a)
  => Prog eff Bool
  -> Handler '[Act a, Par, Res a] eff '[C.CResT a] b (ActsMb a b)
resumpWithM pb = handler (\oalg -> runWithM (eval oalg pb))  (\_ -> resumpAlg)

-- | Resumption-based handler of concurrency with joined parallel composition.
-- Non-deterministic branches are explored by backtracking, resulting in a list
-- of all (successful) traces.
jresump :: forall a b . Action a => Handler '[Act a, JPar, Res a] '[] '[C.CResT a] b (C.ListActs a b)
jresump = handler' runAll jresumpAlg

-- | Resumption-based handler of concurrency with joined parallel composition.
-- Non-deterministic choices are resolved with the given list of Booleans.
jresumpWith :: forall a b. Action a => [Bool] -> Handler '[Act a, JPar, Res a] '[] '[C.CResT a] b (ActsMb a b)
jresumpWith choices = handler' (runWith choices) jresumpAlg

-- | Resumption-based handler of concurrency with joined parallel composition.
-- Non-deterministic choices are resolved with the given program (of effect @eff@).
jresumpWithM
  :: forall eff a b.
     (Action a)
  => Prog eff Bool
  -> Handler '[Act a, JPar, Res a] eff '[C.CResT a] b (ActsMb a b)
jresumpWithM pb = handler (\oalg -> runWithM (eval oalg pb)) (\_ -> jresumpAlg)


-- * IO-based Handlers

-- $ioBasedHandler
--
-- For the actions of type `CCSAction n`, we can implement concurrency using the
-- built-in concurrency API of Haskell from "Control.Concurrent". The idea is
-- that every action @a@ is implemented as a pair of semaphores @s1@ and @s2@,
-- performing this action @a@ is implemented as @do waitQSem s1; signalQSem s2@,
-- while performing the dual of @a@ is implemented as @do signalQSem s1; waitQSem
-- s2@. In this way, performing @a@ and the dual of @a@ are always synchronised.

-- | Mapping an action to two semaphores.
type QSemMap a = M.Map a (QSem, QSem)

-- | IO-based handler of concurrency. The effect of restriction is translated
-- to creating new semaphores, and performing (synchronised) actions is translated
-- to operations on semaphores.
-- Note that operations t`Par` and t`JPar` are part of the IO-effects in "Control.Effect.IO",
-- so they don't need to be handled here.
ccsByQSem
  :: forall n a.
     Ord n
  => Handler '[Act (CCSAction n), Res (CCSAction n)]
             '[Alg IO]
             '[R.ReaderT (QSemMap n), E.ExceptT String]
             a
             (Either String a)
ccsByQSem = (interpretM (\o -> actionAlg o :#. resAlg o) \\ R.reader M.empty) \\ E.except where
  actionAlg
    :: Monad m
    => Algebra '[ R.Ask (QSemMap n), R.Local (QSemMap n), E.Throw String, Alg IO ] m
    -> forall x. Act (CCSAction n) m x
    -> m x
  actionAlg oalg (Act (Action n) p) = eval oalg $ do
    m <- R.ask @(QSemMap n)
    case M.lookup n m of
      Just (s1, s2) -> do io (QSem.waitQSem s1); io (QSem.signalQSem s2)
      Nothing  -> E.throw "Channel used before creation!"
    return p
  actionAlg oalg (Act (CoAction n) p) = eval oalg $ do
    m <- R.ask @(QSemMap n)
    case M.lookup n m of
      Just (s1, s2) -> do io (QSem.signalQSem s1); io (QSem.waitQSem s2)
      Nothing  -> E.throw "Channel used before creation!"
    return p

  resAlg
    :: Monad m
    => Algebra '[ R.Ask (QSemMap n), R.Local (QSemMap n), E.Throw String, Alg IO] m
    -> forall x. Res (CCSAction n) m x
    -> m x
  resAlg oalg (Res a p) = do
    (m, s1, s2) <- eval oalg $ do
       m <- R.ask @(QSemMap n)
       s1 <- io (QSem.newQSem 0)
       s2 <- io (QSem.newQSem 0)
       return (m, s1, s2)
    let m' = M.insert (getActionName a) (s1, s2) m
    R.localM oalg (const m') p

-- | Staged version of `ccsByQSemC`.
ccsByQSemC
  :: forall n a.
     Ord n
  => HandlerC '[Act (CCSAction n), Res (CCSAction n)]
              '[Alg IO]
              '[R.ReaderT (QSemMap n), E.ExceptT String]
              a
              (Either String a)
ccsByQSemC = (interpretMC (\o -> actionAlg o :#.$ resAlg o) \\$ R.readerC [||M.empty||]) \\$ E.exceptC where
  actionAlg
    :: Monad m
    => AlgebraC '[ R.Ask (QSemMap n), R.Local (QSemMap n), E.Throw String, Alg IO ] m
    -> CodeQ (Act (CCSAction n) m -.> m)
  actionAlg oalg = [|| NT $ \(Act a p) ->
    case a of
      (Action n) ->
        do m <- $$(callMC @(R.Ask (QSemMap n)) oalg) (R.Ask id)
           case M.lookup n m of
             Just (s1, s2) -> do $$(callMC oalg) (Alg (QSem.waitQSem s1)); $$(callMC oalg) (Alg (QSem.signalQSem s2))
             Nothing  -> $$(callMC oalg) (E.Throw "Channel used before creation!")
           return p
      (CoAction n) ->
        do m <- $$(callMC @(R.Ask (QSemMap n)) oalg) (R.Ask id)
           case M.lookup n m of
             Just (s1, s2) -> do $$(callMC oalg) (Alg (QSem.signalQSem s1)); $$(callMC oalg) (Alg (QSem.waitQSem s2))
             Nothing  -> $$(callMC oalg) (E.Throw "Channel used before creation!")
           return p
     ||]

  resAlg
    :: Monad m
    => AlgebraC '[ R.Ask (QSemMap n), R.Local (QSemMap n), E.Throw String, Alg IO] m
    -> CodeQ (Res (CCSAction n) m -.> m)
  resAlg oalg = [|| NT $ \(Res a p) -> do
      m <- $$(callMC @(R.Ask (QSemMap n)) oalg) (R.Ask id)
      s1 <- $$(callMC oalg) (Alg (QSem.newQSem 0))
      s2 <- $$(callMC oalg) (Alg (QSem.newQSem 0))
      let m' = M.insert (getActionName a) (s1, s2) m
      $$(callMC oalg) (R.Local (const m') p)
    ||]


-- | Interprets t`Control.Effect.Concurrency.Par` using the native concurrency API
-- from `Control.Concurrent`.
parIOAlg :: Algebra '[Par] IO
parIOAlg = singAlg $ \(Par l r) -> Control.Concurrent.forkIO (fmap (const ()) r) >> l

-- | Staged version of `parIOAlg`
parIOAlgC :: AlgebraC '[Par] IO
parIOAlgC = [|| NT $ \(Par l r) -> Control.Concurrent.forkIO (fmap (const ()) r) >> l ||] :#$ emptyAlgC

-- | Interprets t`Control.Effect.Concurrency.JPar` using the native concurrency API
-- from "Control.Concurrent". The result from the child thread is passed back to the
-- main thread using @MVar@.
jparIOAlg :: Algebra '[JPar] IO
jparIOAlg = singAlg $ \(JPar l r c) -> jparIOImp l r c

-- | Staged version of `jparIOAlg`
jparIOAlgC :: AlgebraC '[JPar] IO
jparIOAlgC = [|| NT $ \(JPar l r c) -> jparIOImp l r c ||] :#$ emptyAlgC

jparIOImp :: IO x -> IO x -> (JPar_ x -> b) -> IO b
jparIOImp l r c =
  do
    m <- MVar.newEmptyMVar
    Control.Concurrent.forkIO $
      do y <- r; MVar.putMVar m y
    x <- l
    y' <- MVar.takeMVar m
    return (c (JPar_ x y'))