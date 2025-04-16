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
{-# LANGUAGE DataKinds #-}
module Control.Effect.Concurrency (
  -- * Syntax
  -- | Signatures and operations are in this module.
  module Control.Effect.Concurrency.Types,

  -- * Semantics

  -- ** Resumption-based handlers 
  resump,
  resumpWith,
  resumpWithM,
  resumpAlg,
  jresumpAlg,
  jresump,
  jresumpWith,

  -- ** IO-based handlers
  ccsByQSem,

  -- ** Re-exported types used by handlers
  Control.Monad.Trans.CRes.ListActs (..),
  Control.Monad.Trans.CRes.ActsMb (..),
  Control.Monad.Trans.CRes.CResT (..),
  ) where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped
import Control.Effect.Distributive
import Control.Effect.Concurrency.Types
import Control.Effect.IO (NewQSem, SignalQSem, WaitQSem, newQSem, signalQSem, waitQSem)
import qualified Control.Effect.Reader as R
import qualified Control.Effect.Except as E
import qualified Control.Monad.Trans.CRes as C
import Control.Concurrent.QSem (QSem)
import Control.Monad.Trans.CRes 
import qualified Data.Map as M
import Data.HFunctor

-- | Algebra for the resumption-based handler of t`Par`, t`Act`, and t`Res`.
resumpAlg :: (Action a, Monad m) => Algebra '[Act a, Par, Res a] (C.CResT a m)
resumpAlg eff
  | Just (Alg (Act a p)) <- prj eff = prefix a (return p)
  | Just (Scp (Par l r)) <- prj eff = C.par l r
  | Just (Scp (Res a p)) <- prj eff = C.res a p

-- | Algebra for the resumption-based handler of t`JPar`, t`Act`, and t`Res`.
jresumpAlg :: (Action a, Monad m) => Algebra '[Act a, JPar, Res a] (C.CResT a m)
jresumpAlg eff
  | Just (Alg (Act a p)) <- prj eff = prefix a (return p)
  | Just (Distr (JPar l r) c) <- prj eff = fmap (\(x, y) -> c (JPar x y)) (C.jpar l r)
  | Just (Scp (Res a p)) <- prj eff = C.res a p

-- | Resumption-based handler of concurrency. Non-deterministic branches are explored 
-- by backtracking, resulting in a list of all (successful) traces.
resump :: forall a. Action a => Handler '[Act a, Par, Res a] '[] (C.CResT a) (C.ListActs a) 
resump = handler runAll (\_ -> resumpAlg)

-- | Resumption-based handler of concurrency. Non-deterministic choices are resolved
-- with the given list Booleans.
resumpWith :: forall a. Action a => [Bool] -> Handler '[Act a, Par, Res a] '[] (C.CResT a) (ActsMb a)
resumpWith choices = handler (runWith choices) (\_ -> resumpAlg)

-- | Resumption-based handler of concurrency. Non-deterministic choices are resolved
-- with the given program (of effect @sig@).
resumpWithM :: forall sig a. 
               ( HFunctor (Effs sig) , Action a ) 
            => Prog sig Bool -> Handler '[Act a, Par, Res a] sig (C.CResT a) (ActsMb a)
resumpWithM pb = Handler (\oalg -> runWithM (eval oalg pb))  (\_ -> resumpAlg)

-- | Resumption-based handler of concurrency with joined parallel composition.
-- Non-deterministic branches are explored by backtracking, resulting in a list 
-- of all (successful) traces.
jresump :: forall a. Action a => Handler '[Act a, JPar, Res a] '[] (C.CResT a) (C.ListActs a) 
jresump = handler runAll (\_ -> jresumpAlg)

-- | Resumption-based handler of concurrency with joined parallel composition. 
-- Non-deterministic choices are resolved with the given list Booleans.
jresumpWith :: forall a. Action a => [Bool] -> Handler '[Act a, JPar, Res a] '[] (C.CResT a) (ActsMb a)
jresumpWith choices = handler (runWith choices) (\_ -> jresumpAlg)

-- | Resumption-based handler of concurrency with joined parallel composition. 
-- Non-deterministic choices are resolved with the given program (of effect @sig@).
jresumpWithM :: forall sig a. 
                ( HFunctor (Effs sig) , Action a ) 
             => Prog sig Bool -> Handler '[Act a, JPar, Res a] sig (C.CResT a) (ActsMb a)
jresumpWithM pb = Handler (\oalg -> runWithM (eval oalg pb)) (\_ -> jresumpAlg)

type QSemMap a = M.Map a (QSem, QSem)

-- | IO-based handler of concurrency. The effect of restriction is translated
-- to creating new semaphores, and performing (synchronised) actions is translated 
-- to operations on semaphores. 
-- Note that operations t`Par` and t`JPar` are part of the IO-effects in "Control.Effect.IO",
-- so they don't need to be handled here.
ccsByQSem :: forall n. Ord n 
          => Handler '[Act (CCSAction n), Res (CCSAction n)]
                     '[NewQSem, WaitQSem, SignalQSem]
                     (R.ReaderT (QSemMap n) `ComposeT` (E.ExceptT String))
                     (Either String)
ccsByQSem = (interpretM alg ||> R.reader M.empty) ||> E.except where
  alg :: Monad m => Algebra '[ R.Ask (QSemMap n), R.Local (QSemMap n)
                             , NewQSem, WaitQSem, SignalQSem
                             , E.Throw String 
                             ] m
                 -> Algebra '[Act (CCSAction n), Res (CCSAction n)] m
  alg oalg op
    | Just (Alg (Act (Action n) p))   <- prj op = 
        eval oalg $ do m <- R.ask @(QSemMap n) 
                       case M.lookup n m of
                         Just (s1, s2) -> do waitQSem s1; signalQSem s2
                         Nothing  -> E.throw "Channel used before creation!"
                       return p
    | Just (Alg (Act (CoAction n) p)) <- prj op =
        eval oalg $ do m <- R.ask @(QSemMap n) 
                       case M.lookup n m of
                         Just (s1, s2) -> do signalQSem s1; waitQSem s2
                         Nothing  -> E.throw "Channel used before creation!"
                       return p
    | Just (Scp (Res a p)) <- prj op =
        do (m, s1, s2) <- eval oalg $ 
              do m <- R.ask @(QSemMap n)
                 s1 <- newQSem 0
                 s2 <- newQSem 0
                 return (m, s1, s2)
           let m' = M.insert (getActionName a) (s1, s2) m
           callM' oalg (Scp (R.Local (const m') p))