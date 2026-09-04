{-|
Module      : Control.Effect.IO
Description : Effects for input/output
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides effects from Haskell's native `IO` monad.
To invoke an IO-action in an effectful program, use the function `io`.
To handle programs with IO, there are currently two ways:

  1. Use the function `handleIO` or `handleIO'` (both are specialisations
     of `handleMFwds`).

  2. Use the function `handle` but have the handler `constIO` at the bottom
     of the handler stack.

These two ways have no difference in terms of expressivity or performance, and
which one to use is only a matter of taste.
-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DerivingVia  #-}

module Control.Effect.IO (
  -- * Syntax
  -- ** Operations
  Alg (..),
  IO,
  io, ioM,

  -- * Semantics
  -- ** Handlers
  constIO,

  -- ** Carriers
  ConstIO (..),

  -- * Evaluation
  evalIO,
  handleIO,
  handleIO',

  -- * Algebras
  ioAlg, ioAlgC
)
  where

import Control.Effect
import Control.Effect.Internal.Handler
import Control.Effect.Family.Algebraic
import Data.List.Kind

-- | Interprets IO operations using their standard semantics in `IO`.
ioAlg :: Algebra '[Alg IO] IO
ioAlg = nativeAlg

-- | Staged version of `ioAlgC`.
ioAlgC :: AlgebraC '[Alg IO] IO
ioAlgC = nativeAlgC

-- | Treating an IO computation as an operation of signature `Alg IO`.
io :: IO a -> a ! '[Alg IO]
io op = call (Alg op)

-- | Treating an IO computation as an operation of signature `Alg IO`.
ioM :: (Alg IO `Member` effs) => Algebra effs m -> IO a -> m a
ioM alg op = callM alg (Alg op)

-- | A constant carrier transformer. This is useful as the final carrier in a
-- handler stack when all remaining operations are to be implemented on the
-- native IO-monad.
--
-- It is not a monad transformer: there is no general way to lift an arbitrary
-- lower-monad action into `IO`.
newtype ConstIO m a = ConstIO { runConstIO :: IO a }
  deriving (Functor, Applicative, Monad) via IO

-- | Handling @Alg IO@ on the `IO` monad.
--
-- This handler is intended to be used as the final handler of a stack, for example
-- @handle (h |> constIO) p@. Any effects handled after this handler are ignored.
constIO :: Handler '[Alg IO] '[] '[ConstIO] a (IO a)
constIO = Handler run alg
  where
    run :: Runner '[] '[ConstIO] a (IO a) Monad
    run = Runner (\_ -> pure . runConstIO)

    alg :: AlgTrans '[Alg IO] '[] '[ConstIO] Monad
    alg = algTrans1 (\_ (Alg iox) -> ConstIO iox)

-- | @`evalIO` p@ evaluates all IO operations in @p@ in the `IO` monad
-- using their standard semantics.
evalIO :: Prog '[Alg IO] a -> IO a
evalIO = eval ioAlg

-- | @`handleIO` h p@ evaluates @p@ using the handler @h@. The handler is
-- allowed to emit the operation @Alg IO@ and the program can use @Alg IO@ too.
handleIO
  :: forall effs oeffs ts a b.
     ( Monad (Apply ts IO)
     , ForwardsM '[Alg IO] ts
     , Members oeffs '[Alg IO]
     , HandleM# effs '[Alg IO] )
  => Handler effs oeffs ts a b
  -> Prog (effs `Union` '[Alg IO]) a
  -> IO b
handleIO = handleM @effs ioAlg

type HandleIO# effs oeffs xeffs =
  ( Members (xeffs :\\ effs) xeffs )

-- | @`handleIO'` h p@ evaluates @p@ using the handler @h@. The handler may
-- output some effects that are a subset of the IO effects and additionally
-- the program may also use a subset @xsigs@ of the IO effects (which must
-- be forwardable through the monad transformer @ts@).
-- The type argument @xsigs@ usually can't be inferred and needs to be given
-- explicitly.
-- This function is useful when you want to use some non-algebraic operations
-- that come with the IO-monad. Otherwise `handleIO` should be used.
handleIO'
  :: forall xeffs ioeff effs oeffs ts a b.
     ( Members oeffs ioeff
     , ForwardsM xeffs ts
     , Monad (Apply ts IO)
     , Members xeffs ioeff
     , HandleIO# effs oeffs xeffs )
  => Proxy xeffs
  -> Algebra ioeff IO
  -> Handler effs oeffs ts a b
  -> Prog (effs `Union` xeffs) a
  -> IO b
handleIO' p ioAlg h = handleMFwds p ioAlg h