{-# LANGUAGE DataKinds #-}
module Control.Effect.Concurrency (
  module Control.Effect.Concurrency.Types,
  Control.Monad.Trans.CRes.ListActs (..),
  Control.Monad.Trans.CRes.ActsMb (..),
  Control.Monad.Trans.CRes.CResT (..),

  resumpAlg,
  resump,
  resumpWith,
  jresumpAlg,
  jresump,
  jresumpWith,
  ccsByQSem,
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

resumpAlg :: (Action a, Monad m) => Algebra '[] m -> Algebra '[Act a, Par, Res a] (C.CResT a m)
resumpAlg _ eff
  | Just (Alg (Act a p)) <- prj eff = prefix a (return p)
  | Just (Scp (Par l r)) <- prj eff = C.par l r
  | Just (Scp (Res a p)) <- prj eff = C.res a p

jresumpAlg :: (Action a, Monad m) => Algebra '[] m -> Algebra '[Act a, JPar, Res a] (C.CResT a m)
jresumpAlg _ eff
  | Just (Alg (Act a p)) <- prj eff = prefix a (return p)
  | Just (Distr (JPar l r) c) <- prj eff = fmap (\(x, y) -> c (JPar x y)) (C.jpar l r)
  | Just (Scp (Res a p)) <- prj eff = C.res a p

resump :: forall a. Action a => Handler '[Act a, Par, Res a] '[] (C.CResT a) (C.ListActs a) 
resump = handler runAll resumpAlg

resumpWith :: forall a. Action a => [Bool] -> Handler '[Act a, Par, Res a] '[] (C.CResT a) (ActsMb a)
resumpWith choices = handler (runWith choices) resumpAlg

jresump :: forall a. Action a => Handler '[Act a, JPar, Res a] '[] (C.CResT a) (C.ListActs a) 
jresump = handler runAll jresumpAlg

jresumpWith :: forall a. Action a => [Bool] -> Handler '[Act a, JPar, Res a] '[] (C.CResT a) (ActsMb a)
jresumpWith choices = handler (runWith choices) jresumpAlg

type QSemMap a = M.Map a (QSem, QSem)

ccsByQSem :: forall n. Ord n 
          => Handler '[Act (CCSAction n), Res (CCSAction n)]
                     '[NewQSem, WaitQSem, SignalQSem]
                     (R.ReaderT (QSemMap n) `ComposeT` (E.ExceptT String))
                     (Either String)
ccsByQSem = interpretM alg ||> R.reader M.empty ||> E.except where
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