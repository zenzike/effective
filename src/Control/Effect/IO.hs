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
  getLine, putStrLn, getCPUTime,

  -- ** Signatures
  GetLine, GetLine_(..),
  PutStrLn, PutStrLn_(..),
  GetCPUTime, GetCPUTime_(..),

  -- * Semantics
  -- * Evaluation
  evalIO,
  handleIO,

  -- * Algebras
  ioAlg,
  putStrLnAlg,
  getLineAlg,
  getCPUTimeAlg,
)
  where

import Control.Effect
import Control.Effect.Algebraic

import GHC.TypeLits

import qualified System.CPUTime
import Data.List.Kind

import Prelude hiding (getLine, putStrLn)
import qualified Prelude as Prelude

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

-- | Signature for `Control.Effect.IO.getCPUTime`.
type GetCPUTime = Alg (GetCPUTime_)
-- | Underlying signature for `Control.Effect.IO.getCPUTime`.
data GetCPUTime_ k = GetCPUTime (Integer -> k) deriving Functor

-- | Returns the number of picoseconds CPU time used by the current
-- program.
getCPUTime :: Members '[GetCPUTime] sig => Prog sig Integer
getCPUTime = call (Alg (GetCPUTime return))

-- | Interprets IO operations using their standard semantics in `IO`.
ioAlg :: Algebra [GetLine, PutStrLn, GetCPUTime] IO
ioAlg = getLineAlg # putStrLnAlg # getCPUTimeAlg

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

-- | Interprets `Control.Effect.IO.getCPUTime` using `System.CPUTime.getCPUTime` from "System.CPUTime".
getCPUTimeAlg :: Algebra '[GetCPUTime] IO
getCPUTimeAlg eff
  | Just (Alg (GetCPUTime x)) <- prj eff =
      do time <- System.CPUTime.getCPUTime
         return (x time)

-- | @`evalIO` p@ evaluates all IO operations in @p@ in the `IO` monad
-- using their standard semantics.
evalIO :: Prog [GetLine, PutStrLn, GetCPUTime] a -> IO a
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
    , xeffs ~ '[GetLine, PutStrLn, GetCPUTime]
    , KnownNat (Length effs))
  => Handler effs oeffs t f
  -> Prog (effs `Union` xeffs) a -> IO (Apply f a)
handleIO = handleM ioAlg
