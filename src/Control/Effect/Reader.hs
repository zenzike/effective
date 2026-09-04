{-|
Module      : Control.Effect.Reader
Description : Effects for the reader monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides the effect of reading an environment variable (i.e. the
effect implemented by the reader monad). There are two operations: an algebraic
operation `ask` for reading the environment and a scoped operation `local` for
binding a new value locally.
-}

module Control.Effect.Reader (
  -- * Syntax
  -- ** Operations
-- | Read the value of the environment
  ask,
  askP,
  askM,
  asks,

-- | Execute a computation in a transformed environment
  local,
  localP,
  localM,
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
  askN, localN,
#endif

  -- ** Signatures
  Ask, Ask_(..), pattern Ask,
  Local, Local_(..), pattern Local,

  -- * Semantics
  -- ** Handlers
  reader,
  reader',
  asker,
  readerC,
  askerC,

  -- ** Algebras
  readerAT,
  askerAT,

  -- ** Underlying monad transformers
  R.ReaderT(..),
  )
  where

import Control.Effect
import Data.Functor.Unary

import qualified Control.Monad.Trans.Reader as R

-- | The operation of asking the environment (of type @r@).
$(makeGen [e| ask :: forall r. r |])

-- | Retrieve a function of the current environment.
{-# INLINE asks #-}
asks
  :: Member (Ask r) effs
  => (r -> a) -- ^ The selector function to apply to the environment
  -> Prog effs a
asks f = fmap f ask

$(makeScp [e| local :: forall r. (r -> r) ~> 1 |])

instance Unary (Local_ r) where
  get (Local_ _ x) = x

{-# INLINE askAlg #-}
askAlg :: Monad m => Ask r (R.ReaderT r m) b -> R.ReaderT r m b
askAlg (Ask p) = do r <- R.ask; return (p r)

{-# INLINE localAlg #-}
localAlg :: Local r (R.ReaderT r m) a -> R.ReaderT r m a
localAlg (Local f p) = R.local f p

-- | The algebra for the 'reader' handler.
{-# INLINE readerAlg #-}
readerAlg :: Monad m => Algebra [Ask r, Local r] (R.ReaderT r m)
readerAlg = askAlg :#. localAlg

-- | An algebra transformer based on t`R.ReaderT`.
{-# INLINE readerAT #-}
readerAT :: AlgTrans '[Ask r, Local r] '[] '[R.ReaderT r] Monad
readerAT = algTrans' readerAlg

-- | An algebra transformer for t`Ask` with a fixed value. This is faster
-- than `readerAT` but it doesn't support t`Local`.
{-# INLINE askerAT #-}
askerAT :: r -> AlgTrans '[Ask r] '[] '[] Monad
askerAT r = interpretAT1 (\(Ask k) -> return (k r))

-- | The `reader` handler supplies a static environment @r@ to the program
-- that can be accessed with `ask`, and locally transformed with `local`.
{-# INLINE reader #-}
reader :: r -> Handler [Ask r, Local r] '[] '[R.ReaderT r] a a
reader r = handler' (flip R.runReaderT r) readerAlg

-- | The `reader'` handler supplies an environment @r@ computed using the
-- output effects to the program that can be accessed with `ask`, and
-- locally transformed with `local`.
{-# INLINE reader' #-}
reader'
  :: forall oeffs r a.
     (forall m. Monad m => Algebra oeffs m -> m r)
  -> Handler [Ask r, Local r] oeffs '[R.ReaderT r] a a
reader' mr = handler run (\_ -> readerAlg) where
  run
    :: forall m.
       Monad m
    => Algebra oeffs m
    -> (R.ReaderT r m a -> m a)
  run oalg rmx = do r <- mr oalg
                    x <- R.runReaderT rmx r
                    return x

-- | A handler of t`Ask` by supplying a fixed value. This is faster than `reader`
-- but it does not support t`Local`.
{-# INLINE asker #-}
asker :: r -> Handler '[Ask r] '[] '[] a a
asker r = interpret1 $ \(Ask k) -> return (k r)

-- * Handlers for lightweight staging
--------------------------------------------------------------------------------

-- | Staged version of `reader`.
readerC :: CodeQ r -> HandlerC [Ask r, Local r] '[] '[R.ReaderT r] a a
readerC r = HandlerC
  (RunnerC $ \_ -> [|| flip R.runReaderT $$r ||])
  (AlgTransC $ \_ -> [|| NT askAlg ||] :#.$ ([|| NT localAlg ||]))

-- | Staged version of `asker`.
askerC :: CodeQ r -> HandlerC '[Ask r] '[] '[] a a
askerC r = HandlerC (RunnerC $ \_ -> [|| id ||])
  (AlgTransC $ \_ -> ([|| NT $ \(Ask p) -> return (p $$r) ||] :#$ emptyAlgC))