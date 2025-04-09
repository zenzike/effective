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

  -- * Algebras
  ioAlg,
  nativeAlg,
  putStrLnAlg,
  putStrAlg,
  getLineAlg,
  getCPUTimeAlg,
  parAlg,
  newQSemAlg,
  signalQSemAlg,
  waitQSemAlg,
)
  where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped
import Control.Effect.Concurrency.Types (Par, Par_(..))

import qualified System.CPUTime
import qualified Control.Concurrent
import qualified Control.Concurrent.QSem as QSem
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
                  , NewQSem
                  , SignalQSem
                  , WaitQSem
                  ]

-- | Interprets IO operations using their standard semantics in `IO`.
ioAlg :: Algebra IOEffects IO
ioAlg = nativeAlg # getLineAlg # putStrLnAlg # putStrAlg # getCPUTimeAlg # parAlg # newQSemAlg # signalQSemAlg # waitQSemAlg

-- | Treating an IO computation as an operation of signature `Alg IO`. 
liftIO :: Members '[Alg IO] sig => IO a -> Prog sig a
liftIO o = call (Alg (fmap return o))

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

-- | Interprets `Control.Effect.Concurrency.Par` using the native concurrency API. 
-- from `Control.Concurrent`.
parAlg :: Algebra '[Par] IO
parAlg eff
  | Just (Scp (Par l r)) <- prj eff =
      do Control.Concurrent.forkIO (fmap (const ()) r)
         l

-- | Signature for `Control.Effect.IO.NewQSem`.
type NewQSem = Alg (NewQSem_)
-- | Underlying signature for `Control.Effect.IO.NewQSem`.
data NewQSem_ k = NewQSem Int (QSem.QSem -> k) deriving Functor

-- | Create a new quantity semaphore with the given initial quantity,
-- which should be non-negative.
newQSem :: Members '[NewQSem] sig => Int -> Prog sig QSem.QSem
newQSem n = call (Alg (NewQSem n return))

-- | Interprets `Control.Effect.IO.NewQSem` using `Control.Concurrent.QSem.newQSem`.
newQSemAlg :: Algebra '[NewQSem] IO
newQSemAlg eff
  | Just (Alg (NewQSem n x)) <- prj eff =
      do q <- QSem.newQSem n
         return (x q)

-- | Signature for `Control.Effect.IO.SignalQSem`.
type SignalQSem = Alg (SignalQSem_)
-- | Underlying signature for `Control.Effect.IO.SignalQSem`.
data SignalQSem_ k = SignalQSem QSem.QSem k deriving Functor

-- | Signal that a unit of the semaphore is available
signalQSem :: Members '[SignalQSem] sig => QSem.QSem -> Prog sig ()
signalQSem q = call (Alg (SignalQSem q (return ())))

-- | Interprets `Control.Effect.IO.SignalQSem` using `Control.Concurrent.QSem.signalQSem`.
signalQSemAlg :: Algebra '[SignalQSem] IO
signalQSemAlg eff
  | Just (Alg (SignalQSem q x)) <- prj eff =
      do QSem.signalQSem q
         return x

-- | Signature for `Control.Effect.IO.WaitQSem`.
type WaitQSem = Alg (WaitQSem_)
-- | Underlying signature for `Control.Effect.IO.WaitQSem`.
data WaitQSem_ k = WaitQSem QSem.QSem k deriving Functor

-- | Wait for the semaphore to be available.
waitQSem :: Members '[WaitQSem] sig => QSem.QSem -> Prog sig ()
waitQSem q = call (Alg (WaitQSem q (return ())))

-- | Interprets `Control.Effect.IO.WaitQSem` using `Control.Concurrent.QSem.waitQSem`.
waitQSemAlg :: Algebra '[WaitQSem] IO
waitQSemAlg eff
  | Just (Alg (WaitQSem q x)) <- prj eff =
      do QSem.waitQSem q
         return x

-- | @`evalIO` p@ evaluates all IO operations in @p@ in the `IO` monad
-- using their standard semantics.
evalIO :: Prog IOEffects a -> IO a
evalIO = eval ioAlg

-- | @`handleIO` h p@ evaluates @p@ using te handler @h@. Any residual
-- effects are then interpreted in `IO` using their standard semantics.
handleIO
  :: forall effs oeffs t f a xeffs
  . ( Injects oeffs xeffs
    , Injects (xeffs :\\ effs) xeffs
    , Functor f
    , Forwards xeffs t
    , forall m . Monad m => Monad (t m)
    , xeffs ~ IOEffects
    -- , KnownNat (Length effs)
    , Append effs (xeffs :\\ effs)
    , HFunctor (Effs (effs :++ (IOEffects :\\ effs)))
    )

  => Handler effs oeffs t f
  -> Prog (effs `Union` xeffs) a -> IO (Apply f a)
handleIO = handleM ioAlg
