{-|
Module      : Control.Effect.Maybe
Description : Exception throwing without a value
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE LambdaCase #-}

module Control.Effect.Maybe (
  -- * Syntax
  -- ** Operations

  -- | Throwing an exception.
  throw,
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
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Monad.Trans.Maybe

$(makeAlg [e| throw :: 0 |])

$(makeScp [e| catch :: 2 |])


-- | The 'except' handler will interpret @catch p q@ by first trying @p@.
-- If it fails, then @q@ is executed.
except :: Handler [Throw, Catch] '[] '[MaybeT] a (Maybe a)
except = Handler (runner' runMaybeT) exceptAT

-- | The algebra transformer for the 'except' handler.
exceptAT :: AlgTrans [Throw, Catch] '[] '[MaybeT] Monad
exceptAT = AlgTrans $ \oalg op -> case op of
    Throw -> MaybeT (return Nothing)
    (Catch p q) -> MaybeT $ do
       mx <- runMaybeT p
       case mx of
         Nothing -> runMaybeT q
         Just x  -> return (Just x)

-- | The 'retry' handler will interpet @catch p q@  by first trying @p@.
-- If it fails, then @q@ is executed as a recovering clause.
-- If the recovery fails then the computation is failed overall.
-- If the recovery succeeds, then @catch p q@ is attempted again.
retry :: Handler [Throw, Catch] '[] '[MaybeT] a (Maybe a)
retry = Handler (runner' runMaybeT) retryAT

-- | The algebra for the 'retry' handler.
retryAT :: AlgTrans [Throw, Catch] '[] '[MaybeT] Monad
retryAT = algTrans' $ \case
  Throw       -> MaybeT (return Nothing)
  (Catch p q) -> MaybeT $ loop p q where
    loop p q =
      do mx <- runMaybeT p
         case mx of
           Nothing -> do my <- runMaybeT q
                         case my of
                           Nothing -> return Nothing
                           Just y  -> loop p q
           Just x  -> return (Just x)