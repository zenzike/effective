{-|
Module      : Control.Effect.Nondet.List
Description : Effects for nondeterministic computations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides effects and handlers for nondeterministic computations,
including choice and failure.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Nondet.List (
  -- * Syntax
  -- | Signatures and operations are in this module.
  module Control.Effect.Nondet.Operations,

  -- * Semantics
  -- ** Handlers
  nondet, nondetC,
  backtrack, backtrackC,
  nondet', nondetC',
  backtrack', backtrackC',

  -- ** Algebras
  nondetAT, nondetATC,

  -- ** Re-exported carriers
  ListT (..)
) where

import Prelude hiding (or)

import Control.Effect.Nondet.Operations
import Control.Effect hiding (emptyAlg)
import Control.Monad.Trans.List

{-# INLINE emptyAlg #-}
emptyAlg :: forall m a. Monad m => Empty (ListT m) a -> ListT m a
emptyAlg Empty = empty

{-# INLINE chooseAlg #-}
chooseAlg :: Monad m => Choose (ListT m) a -> ListT m a
chooseAlg (Choose xs ys) = xs <|> ys

{-# INLINE nondetOrAlg #-}
nondetOrAlg :: forall m a. Monad m => NondetOr (ListT m) a -> ListT m a
nondetOrAlg (NondetOr xs ys) = pure xs <|> pure ys

{-# INLINE onceAlg #-}
onceAlg :: Monad m => Once (ListT m) a -> ListT m a
onceAlg (Once xs) = ListT $ do
  mx <- runListT xs
  case mx of Nothing       -> return Nothing
             Just (x, mxs) -> return (Just (x, empty))

-- | The `nondet` handler transforms nondeterminism effects t`Empty` and t`Choose`
-- into the t`ListT` monad transformer, which collects all possible results.
nondet :: Handler [Empty, NondetOr] '[] '[ListT] a [a]
nondet = handler' runListT' (emptyAlg :#. nondetOrAlg)

-- | This handler additionally handles t`Once` and the scoped operation `Choose` (the
-- `Alternative` instance on t`Prog` uses `Choose`).
backtrack :: Handler [Empty, Choose, NondetOr, Once] '[] '[ListT] a [a]
backtrack = handler' runListT' (emptyAlg :# chooseAlg :# nondetOrAlg :#. onceAlg)

-- | A variant of `nondet` that additionally handles t`Choose`.
nondet' :: Handler [Empty, Choose, NondetOr] '[] '[ListT] a [a]
nondet' = handler' runListT' (emptyAlg :# chooseAlg :#. nondetOrAlg)

-- | A variant of `backtrack` that does not handle t`Choose` but still
-- supports backtracking.
backtrack' :: Handler [Empty, NondetOr, Once] '[] '[ListT] a [a]
backtrack' = handler' runListT' (emptyAlg :# nondetOrAlg :#. onceAlg)

{-# INLINE nondetAT #-}
-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying `Alternative` instance for @t m@ given by a transformer @t@.
nondetAT :: AlgTrans '[Empty, NondetOr] '[] '[ListT] Monad
nondetAT = algTrans' (emptyAlg :#. nondetOrAlg)

-- Handlers for lightweight staging

-- | Staged version of `nondetAT`.
nondetATC :: AlgTransC '[Empty, NondetOr] '[] '[ListT] Monad
nondetATC = AlgTransC $ \_ ->
  [|| NT emptyAlg ||] :#$ [|| NT nondetOrAlg ||] :#$ emptyAlgC

-- | Staged version of `nondet`
nondetC :: HandlerC [Empty, NondetOr] '[] '[ListT] a [a]
nondetC = HandlerC
  (RunnerC $ \_ -> [|| runListT' ||])
  nondetATC

-- | Staged version of `backtrack`.
backtrackC :: HandlerC [Empty, Choose, NondetOr, Once] '[] '[ListT] a [a]
backtrackC = HandlerC
  (RunnerC $ \_ -> [|| runListT' ||])
  (AlgTransC $ \_ ->
    [|| NT emptyAlg ||] :#$
    [|| NT chooseAlg ||] :#$
    [|| NT nondetOrAlg ||] :#$
    [|| NT onceAlg ||] :#$
    emptyAlgC)

-- | Staged version of `nondet'`.
nondetC' :: HandlerC [Empty, Choose, NondetOr] '[] '[ListT] a [a]
nondetC' = HandlerC
  (RunnerC $ \_ -> [|| runListT' ||])
  (AlgTransC $ \_ ->
    [|| NT emptyAlg ||] :#$
    [|| NT chooseAlg ||] :#$
    [|| NT nondetOrAlg ||] :#$
    emptyAlgC)

-- | Staged version of `backtrack'`.
backtrackC' :: HandlerC [Empty, NondetOr, Once] '[] '[ListT] a [a]
backtrackC' = HandlerC
  (RunnerC $ \_ -> [|| runListT' ||])
  (AlgTransC $ \_ ->
    [|| NT emptyAlg ||] :#$
    [|| NT nondetOrAlg ||] :#$
    [|| NT onceAlg ||] :#$
    emptyAlgC)
