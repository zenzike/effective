{-|
Module      : Control.Effect.Maybe
Description : Exception throwing without a value
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module contains the effects @Throw@ for throwing an exception and @Catch@
for catching the effect. If you need to throw an exception of some type, you may
want to use the interface provided by the module "Control.Effect.Except".
-}

{-# LANGUAGE LambdaCase #-}

module Control.Effect.Maybe (
  -- * Syntax
  -- ** Operations

  -- | Throwing an exception.
  throw,
  throwM,
  throwP,
  -- | @catch p h@ catches the exceptions thrown by @p@ and handles them with @h@.
  catch,
  catchP,
  catchM,
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
  throwN, catchN,
#endif

  -- ** Signatures
  Throw, Throw_(..), pattern Throw,
  Catch, Catch_(..), pattern Catch,

  -- * Semantics
  -- ** Handlers
  except,
  retry,

  -- ** Algebras
  exceptAT,
  retryAT,

  -- ** Underlying monad transformers
  MaybeT(..)
) where

import Control.Effect
import Control.Monad.Trans.Maybe

$(makeAlg [e| throw :: 0 |])

$(makeScp [e| catch :: 2 |])

-- | The 'except' handler will interpret @catch p q@ by first trying @p@.
-- If it fails, then @q@ is executed.
except :: Handler [Throw, Catch] '[] '[MaybeT] a (Maybe a)
except = Handler (runner' runMaybeT) exceptAT

-- | The algebra transformer for the 'except' handler.
exceptAT :: AlgTrans [Throw, Catch] '[] '[MaybeT] Monad
exceptAT = algTrans' $ throwAlg :# catchAlg :# emptyAlg

{-# INLINE throwAlg #-}
throwAlg :: Monad m => Throw f k -> MaybeT m a
throwAlg Throw = MaybeT (return Nothing)

{-# INLINE catchAlg #-}
catchAlg :: Monad m => Catch (MaybeT m) a -> MaybeT m a
catchAlg (Catch p q) = MaybeT $ do
  mx <- runMaybeT p
  case mx of
    Nothing  -> runMaybeT q
    Just x -> return (Just x)

{-# INLINE retryAlg #-}
retryAlg :: Monad m => Catch (MaybeT m) a -> MaybeT m a
retryAlg (Catch p q) = MaybeT $
  let loop p q =
        do mx <- runMaybeT p
           case mx of
             Nothing -> do my <- runMaybeT q
                           case my of
                             Nothing -> return Nothing
                             Just y  -> loop p q
             Just x  -> return (Just x)
  in loop p q

-- | The 'retry' handler will interpret @catch p q@ by first trying @p@.
-- If it fails, then @q@ is executed as a recovery clause.
-- If the recovery fails, then the computation fails overall.
-- If the recovery succeeds, then @catch p q@ is attempted again.
retry :: Handler [Throw, Catch] '[] '[MaybeT] a (Maybe a)
retry = Handler (runner' runMaybeT) retryAT

-- | The algebra for the 'retry' handler.
retryAT :: AlgTrans [Throw, Catch] '[] '[MaybeT] Monad
retryAT = algTrans' $ throwAlg :#. retryAlg

-- Handlers for lightweight staging

-- | Staged version of `except`
exceptC :: HandlerC '[Throw, Catch] '[] '[MaybeT] a (Maybe a)
exceptC = HandlerC
  (RunnerC $ \_ -> [|| runMaybeT ||])
  (AlgTransC $ \_ -> [|| NT throwAlg ||] :#$ [|| NT catchAlg ||] :#$ emptyAlgC)

-- | Staged version of `retry`
retryC :: HandlerC '[Throw, Catch] '[] '[MaybeT] a (Maybe a)
retryC = HandlerC
  (RunnerC $ \_ -> [|| runMaybeT ||])
  (AlgTransC $ \_ -> [|| NT throwAlg ||] :#$ [|| NT retryAlg ||] :#$ emptyAlgC)