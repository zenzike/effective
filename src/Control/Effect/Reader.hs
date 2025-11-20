{-|
Module      : Control.Effect.Reader
Description : Effects for the reader monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Effect.Reader (
  -- * Syntax
  -- ** Operations
-- | Read the value of the environment
  ask,
  askP,
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
  readerAsk,
  asker,

  -- ** Algebras
  readerAT,
  readerAskAT,

  -- ** Underlying monad transformers
  R.ReaderT(..),
) where

import Control.Effect
import Control.Effect.Internal.AlgTrans
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Data.Functor.Unary

import qualified Control.Monad.Trans.Reader as R

-- | The operation of asking the environment (of type @r@).
$(makeGen [e| ask :: forall r. r |])

-- | Retrieve a function of the current environment.
{-# INLINE asks #-}
asks :: Member (Ask r) sig
  => (r -> a) -- ^ The selector function to apply to the environment
  -> Prog sig a
asks f = fmap f ask

$(makeScp [e| local :: forall r. (r -> r) -> 1 |])

instance Unary (Local_ r) where
  get (Local_ _ x) = x

-- | The `reader` handler supplies a static environment @r@ to the program
-- that can be accessed with `ask`, and locally transformed with `local`.
{-# INLINE reader #-}
reader :: r -> Handler [Ask r, Local r] '[] '[R.ReaderT r] a a
reader r = handler' (flip R.runReaderT r) (\_ -> readerAlg)
--       = (\_ -> readerAlg) #: runner (flip R.runReaderT r)

-- | The `reader'` handler supplies an environment @r@ computed using the
-- output effects to the program that can be accessed with `ask`, and
-- locally transformed with `local`.
{-# INLINE reader' #-}
reader' :: forall oeffs r a . (forall m . Monad m => Algebra oeffs m -> m r)
        -> Handler [Ask r, Local r] oeffs '[R.ReaderT r] a a
reader' mr = handler run (\_ -> readerAlg) where
  run :: forall m . Monad m => Algebra oeffs m
      -> (R.ReaderT r m a -> m a)
  run oalg rmx = do r <- mr oalg
                    x <- R.runReaderT rmx r
                    return x

-- | The algebra for the 'reader' handler.
{-# INLINE readerAlg #-}
readerAlg
  :: Monad m => Algebra [Ask r, Local r] (R.ReaderT r m)
readerAlg (Ask p)     = do r <- R.ask; return (p r)
readerAlg (Local f p) = R.local f p

readerAT :: AlgTrans '[Ask r, Local r] '[] '[R.ReaderT r] Monad
readerAT = AlgTrans (\_ -> readerAlg)

readerAskAT :: AlgTrans '[Ask r] '[] '[R.ReaderT r] Monad
readerAskAT = weakenIEffs readerAT

readerAsk :: r -> Handler '[Ask r] '[] '[R.ReaderT r] a a
readerAsk r = handler' (flip R.runReaderT r) (getAT readerAskAT)

asker :: r -> Handler '[Ask r] '[] '[] a a
asker r = interpret (\(Ask k) -> return (k r))