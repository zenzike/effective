{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=500 #-}
{-|
Module      : Control.Effect.IO
Description : Effects for input/output
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE MonoLocalBinds #-}
#if __GLASGOW_HASKELL__ <= 902
{-# LANGUAGE TypeFamilies #-}
#endif

module Control.Effect.IO (
  -- * Syntax
  -- ** Operations
  liftIO, getLine, putStrLn, putStr, getCPUTime, newQSem, signalQSem, waitQSem,

  -- ** Signatures
  IOEffects,
  GetLine, GetLine_(..),
  PutStrLn, PutStrLn_(..),
  PutStr, PutStr_(..),
  GetCPUTime, GetCPUTime_(..),
  NewQSem, NewQSem_(..),
  SignalQSem, SignalQSem_(..),
  WaitQSem, WaitQSem_(..),

  -- * Semantics
  -- * Evaluation
  evalIO,
  handleIO,
  handleIO',
  handleIOApp,

  -- * Algebras
  ioAlg,
  nativeAlg,
  putStrLnAlg,
  putStrAlg,
  getLineAlg,
  getCPUTimeAlg,
  parAlg,
  jparAlg,
  newQSemAlg,
  signalQSemAlg,
  waitQSemAlg,
)
  where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Family.Distributive
import Control.Effect.Concurrency.Types (Par, Par_(..), JPar, JPar_(..))

import qualified System.CPUTime
import qualified Control.Concurrent
import qualified Control.Concurrent.QSem as QSem
import qualified Control.Concurrent.MVar as MVar
import Data.List.Kind
import Data.HFunctor

import Prelude hiding (getLine, putStrLn, putStr)
import qualified Prelude as Prelude

-- | The effects operations that the IO monad supports natively
type IOEffects = '[ Alg IO
                  , GetLine
                  , PutStrLn
                  , PutStr
                  , GetCPUTime
                  , Par
                  , JPar
                  , NewQSem
                  , SignalQSem
                  , WaitQSem
                  ]

-- | Interprets IO operations using their standard semantics in `IO`.
ioAlg :: Algebra IOEffects IO
ioAlg = nativeAlg # getLineAlg # putStrLnAlg # putStrAlg # getCPUTimeAlg 
        # parAlg # jparAlg # newQSemAlg # signalQSemAlg # waitQSemAlg

-- | Treating an IO computation as an operation of signature `Alg IO`. 
liftIO :: Members '[Alg IO] sig => IO a -> Prog sig a
liftIO o = call' (Alg o)

-- | Algebra for the generic algebraic IO effect
nativeAlg :: Algebra '[Alg IO] IO
nativeAlg op
  | Just (Alg (op')) <- prj op = op'

-- | Signature for `Control.Effects.IO.getLine`.
type GetLine = Alg GetLine_
-- | Underlying signature for `Control.Effects.IO.getLine`.
data GetLine_ k  = GetLine (String -> k) deriving Functor

-- | Read a line from from standard input device.
getLine :: Members '[GetLine] sig => Prog sig String
getLine = call (Alg (GetLine return))

-- | Signature for `Control.Effect.IO.putStrLn`.
type PutStrLn = Alg PutStrLn_
-- | Underlying signature for `Control.Effect.IO.putStrLn`.
data PutStrLn_ k = PutStrLn String k     deriving Functor

-- | Write a string to the standard output device, and add a newline character.
putStrLn :: Members '[PutStrLn] sig => String -> Prog sig ()
putStrLn str = call (Alg (PutStrLn str (return ())))

-- | Signature for `Control.Effect.IO.putStr`.
type PutStr = Alg PutStr_
-- | Underlying signature for `Control.Effect.IO.putStr`.
data PutStr_ k = PutStr String k     deriving Functor

-- | Write a string to the standard output device.
putStr :: Members '[PutStr] sig => String -> Prog sig ()
putStr str = call (Alg (PutStr str (return ())))

-- | Signature for `Control.Effect.IO.getCPUTime`.
type GetCPUTime = Alg (GetCPUTime_)
-- | Underlying signature for `Control.Effect.IO.getCPUTime`.
data GetCPUTime_ k = GetCPUTime (Integer -> k) deriving Functor

-- | Returns the number of picoseconds CPU time used by the current
-- program.
getCPUTime :: Members '[GetCPUTime] sig => Prog sig Integer
getCPUTime = call (Alg (GetCPUTime return))

-- | Interprets `Control.Effects.IO.getLine` using `Prelude.getLine` from "Prelude".
getLineAlg :: Algebra '[GetLine] IO
getLineAlg eff
  | Just (Alg (GetLine x)) <- prj eff =
      do str <- Prelude.getLine
         return (x str)

-- | Interprets `Control.Effect.IO.putStrLn` using `Prelude.putStrLn` from "Prelude".
putStrLnAlg :: Algebra '[PutStrLn] IO
putStrLnAlg eff
  | Just (Alg (PutStrLn str x)) <- prj eff =
      do Prelude.putStrLn str
         return x

-- | Interprets `Control.Effect.IO.putStr` using `Prelude.putStr` from "Prelude".
putStrAlg :: Algebra '[PutStr] IO
putStrAlg eff
  | Just (Alg (PutStr str x)) <- prj eff =
      do Prelude.putStr str
         return x

-- | Interprets `Control.Effect.IO.getCPUTime` using `System.CPUTime.getCPUTime` from "System.CPUTime".
getCPUTimeAlg :: Algebra '[GetCPUTime] IO
getCPUTimeAlg eff
  | Just (Alg (GetCPUTime x)) <- prj eff =
      do time <- System.CPUTime.getCPUTime
         return (x time)

-- | Interprets t`Control.Effect.Concurrency.Par` using the native concurrency API. 
-- from `Control.Concurrent`.
parAlg :: Algebra '[Par] IO
parAlg eff
  | Just (Scp (Par l r)) <- prj eff =
      do Control.Concurrent.forkIO (fmap (const ()) r)
         l

-- | Interprets t`Control.Effect.Concurrency.JPar` using the native concurrency API. 
-- from "Control.Concurrent". The result from the child thread is passed back to the 
-- main thread using @MVar@.
jparAlg :: Algebra '[JPar] IO
jparAlg eff
  | Just (Distr (JPar l r) c) <- prj eff =
      do m <- MVar.newEmptyMVar
         Control.Concurrent.forkIO $
           do y <- r; MVar.putMVar m y
         x <- l
         y' <- MVar.takeMVar m
         return (c (JPar x y'))

-- | Signature for the operation of creating new semaphores.
type NewQSem = Alg (NewQSem_)
-- | Underlying first-order signature for creating new semaphores.
data NewQSem_ k = NewQSem Int (QSem.QSem -> k) deriving Functor

-- | Create a new quantity semaphore with the given initial quantity,
-- which should be non-negative.
newQSem :: Members '[NewQSem] sig => Int -> Prog sig QSem.QSem
newQSem n = call (Alg (NewQSem n return))

-- | Interprets t`Control.Effect.IO.NewQSem` using `Control.Concurrent.QSem.newQSem`.
newQSemAlg :: Algebra '[NewQSem] IO
newQSemAlg eff
  | Just (Alg (NewQSem n x)) <- prj eff =
      do q <- QSem.newQSem n
         return (x q)

-- | Signature for the operation of signalling a semaphore.
type SignalQSem = Alg (SignalQSem_)

-- | Underlying first-order signature for the operation of signalling a semaphore.
data SignalQSem_ k = SignalQSem QSem.QSem k deriving Functor

-- | Signal that a unit of the semaphore is available
signalQSem :: Members '[SignalQSem] sig => QSem.QSem -> Prog sig ()
signalQSem q = call (Alg (SignalQSem q (return ())))

-- | Interprets t`Control.Effect.IO.SignalQSem` using `Control.Concurrent.QSem.signalQSem`.
signalQSemAlg :: Algebra '[SignalQSem] IO
signalQSemAlg eff
  | Just (Alg (SignalQSem q x)) <- prj eff =
      do QSem.signalQSem q
         return x

-- | Signature for the operation of waiting for a semaphore.
type WaitQSem = Alg (WaitQSem_)

-- | Underlying first-order signature for waiting for semaphores.
data WaitQSem_ k = WaitQSem QSem.QSem k deriving Functor

-- | Wait for the semaphore to be available.
waitQSem :: Members '[WaitQSem] sig => QSem.QSem -> Prog sig ()
waitQSem q = call (Alg (WaitQSem q (return ())))

-- | Interprets t`Control.Effect.IO.WaitQSem` using `Control.Concurrent.QSem.waitQSem`.
waitQSemAlg :: Algebra '[WaitQSem] IO
waitQSemAlg eff
  | Just (Alg (WaitQSem q x)) <- prj eff =
      do QSem.waitQSem q
         return x

-- | @`evalIO` p@ evaluates all IO operations in @p@ in the `IO` monad
-- using their standard semantics.
evalIO :: Prog IOEffects a -> IO a
evalIO = eval ioAlg

type AutoHandleIO effs oeffs xeffs = 
  ( Injects (xeffs :\\ effs) xeffs
  , Append effs (xeffs :\\ effs)
  , HFunctor (Effs (effs `Union` xeffs)))

-- | @`handleIO` h p@ evaluates @p@ using the handler @h@. The handler may
-- output some effects @xeffs@ that are a subset of the IO effects and
-- the program may also use @xeffs@ .
-- The type argument @xeffs@ usually can't be inferred and needs given
-- explicitly. 

handleIO
  :: forall xeffs effs oeffs ts fs a
  . ( Injects oeffs xeffs
    , Forwards xeffs ts
    , Monad (Apply ts IO)
    , Injects xeffs IOEffects
    , AutoHandleIO effs oeffs xeffs )
  => Handler effs oeffs ts fs
  -> Prog (effs `Union` xeffs) a -> IO (Apply fs a)
handleIO = handleM @effs @oeffs @xeffs (ioAlg . injs)

-- | @`handleIO'` h p@ evaluates @p@ using the handler @h@. Any residual
-- effects are then interpreted in `IO` using their standard semantics.
handleIO'
  :: forall effs oeffs ts fs a
  . ( Injects oeffs IOEffects
    , Monad (Apply ts IO)
    , HFunctor (Effs effs) ) 
  => Handler effs oeffs ts fs
  -> Prog effs a -> IO (Apply fs a)
handleIO' = handleM' @effs @oeffs ioAlg


-- | @`handleIO'` h p@ evaluates @p@ using the handler @h@. Any residual
-- effects @xeffs@ are then interpreted in `IO` using their standard semantics.
-- The type argument @xeffs@ usually can't be inferred and needs given
-- explicitly. 
handleIOApp :: forall xeffs effs oeffs ts fs a .
  ( Monad (Apply ts IO)
  , Forwards xeffs ts
  , Injects oeffs xeffs
  , Append effs xeffs
  , HFunctor (Effs (effs :++ xeffs))
  , Injects xeffs IOEffects )
  => Handler effs oeffs ts fs
  -> Prog (effs :++ xeffs) a
  -> IO (Apply fs a)

handleIOApp = handleMApp @effs @oeffs @xeffs (ioAlg . injs) 