{-|
Module      : Control.Effect.Nondet.Logic
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

module Control.Effect.Nondet.Logic (
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
  LogicT (..)
) where

import Control.Effect hiding (emptyAlg)
import Control.Effect.Nondet.Alternative
import Control.Effect.Nondet.Operations
import Control.Monad.Logic hiding (once)
import qualified Control.Monad.Logic as L

{-# INLINE emptyAlg #-}
emptyAlg :: forall m a. Empty (LogicT m) a -> LogicT m a
emptyAlg Empty = empty

{-# INLINE chooseAlg #-}
chooseAlg :: Choose (LogicT m) a -> LogicT m a
chooseAlg (Choose xs ys) = xs <|> ys

{-# INLINE nondetOrAlg #-}
nondetOrAlg :: forall m a. NondetOr (LogicT m) a -> LogicT m a
nondetOrAlg (NondetOr xs ys) = pure xs <|> pure ys

{-# INLINE onceAlg #-}
onceAlg :: Monad m => Once (LogicT m) a -> LogicT m a
onceAlg (Once p) = L.once p

-- | The `nondet` handler transforms nondeterministic effects t`Empty` and t`Choose`
-- into the t`LogicT` monad transformer, which collects all possible results.
nondet :: Handler [Empty, NondetOr] '[] '[LogicT] a [a]
nondet = handler' observeAllT (emptyAlg :#. nondetOrAlg)

-- | This handler additionally handles t`Once` and the scoped operation `Choose` (the
-- `Alternative` instance on t`Prog` uses `Choose`).
backtrack :: Handler [Empty, Choose, NondetOr, Once] '[] '[LogicT] a [a]
backtrack = handler' observeAllT (emptyAlg :# chooseAlg :# nondetOrAlg :#. onceAlg)

-- | A variant of `nondet` that additionally handles t`Choose`.
nondet' :: Handler [Empty, Choose, NondetOr] '[] '[LogicT] a [a]
nondet' = handler' observeAllT (emptyAlg :# chooseAlg :#. nondetOrAlg)

-- | A variant of `backtrack` that does not handle t`Choose` but still
-- supports backtracking.
backtrack' :: Handler [Empty, NondetOr, Once] '[] '[LogicT] a [a]
backtrack' = handler' observeAllT (emptyAlg :# nondetOrAlg :#. onceAlg)

{-# INLINE nondetAT #-}
-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying @Alternative@ instance for @t m@ given by a transformer @t@.
nondetAT :: AlgTrans '[Empty, NondetOr] '[] '[LogicT] Monad
nondetAT = algTrans' (emptyAlg :#. nondetOrAlg)

-- Handlers for lightweight staging

{-# INLINE nondetATC #-}
-- | Staged version of `nondetAT`.
nondetATC :: AlgTransC '[Empty, NondetOr] '[] '[LogicT] Monad
nondetATC = AlgTransC $ \_ ->
  [|| NT emptyAlg ||] :#$ [|| NT nondetOrAlg ||] :#$ emptyAlgC

-- | Staged version of `nondet`.
nondetC :: HandlerC [Empty, NondetOr] '[] '[LogicT] a [a]
nondetC = HandlerC
  (RunnerC $ \_ -> [|| observeAllT ||])
  nondetATC

-- | Staged version of `backtrack`.
backtrackC :: HandlerC [Empty, Choose, NondetOr, Once] '[] '[LogicT] a [a]
backtrackC = HandlerC
  (RunnerC $ \_ -> [|| observeAllT ||])
  (AlgTransC $ \_ ->
    [|| NT emptyAlg ||] :#$
    [|| NT chooseAlg ||] :#$
    [|| NT nondetOrAlg ||] :#$
    [|| NT onceAlg ||] :#$
    emptyAlgC)

-- | Staged version of `nondet'`.
nondetC' :: HandlerC [Empty, Choose, NondetOr] '[] '[LogicT] a [a]
nondetC' = HandlerC
  (RunnerC $ \_ -> [|| observeAllT ||])
  (AlgTransC $ \_ ->
    [|| NT emptyAlg ||] :#$
    [|| NT chooseAlg ||] :#$
    [|| NT nondetOrAlg ||] :#$
    emptyAlgC)

-- | Staged version of `backtrack'`.
backtrackC' :: HandlerC [Empty, NondetOr, Once] '[] '[LogicT] a [a]
backtrackC' = HandlerC
  (RunnerC $ \_ -> [|| observeAllT ||])
  (AlgTransC $ \_ ->
    [|| NT emptyAlg ||] :#$
    [|| NT nondetOrAlg ||] :#$
    [|| NT onceAlg ||] :#$
    emptyAlgC)
