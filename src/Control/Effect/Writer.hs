{-|
Module      : Control.Effect.Writer
Description : Effects for writing values
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides the effect of writing values. There are two operations:
an algebraic operation `tell` for writing a value and a scoped operation
`censor` for transforming the values being written in a scope.
-}

module Control.Effect.Writer (
  -- * Syntax
  -- ** Operations

-- | The @`tell` w@ operation outputs @w@.
  tell,
  tellP,
  tellM,
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
  tellN,
#endif

-- | The @`censor` f p@ operation executes program @p@ with output censored
-- by @f@.
  censor,
  censorP,
  censorM,
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
  censorN,
#endif

  -- ** Signatures
  Tell, Tell_(..), pattern Tell,
  Censor, Censor_(..), pattern Censor,

  -- * Semantics
  -- ** Handlers
  writer,
  writer_,
  writerIO, writerIOC,
  censors,
  uncensors,

  -- ** Algebras
  writerAT,
  censorAT,

  -- ** Underlying monad transformers
  W.WriterT(..)
) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.IO (io)
import Control.Effect.Internal.TH

import qualified Data.Functor.Unary as U
import Data.Tuple (swap)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.Writer as W

-- | The operation of writing an element of type @w@.
$(makeGen [e| tell :: forall w. w ~> () |])

{-# INLINE tellAlg #-}
tellAlg :: (Monad m, Monoid w) => Tell w (W.WriterT w m) x -> W.WriterT w m x
tellAlg (Tell w x) = do W.tell w; return x

-- | The algebra transformer for the `writer` handler.
writerAT :: Monoid w => AlgTrans '[Tell w] '[] '[W.WriterT w] Monad
writerAT = algTrans1 (\_ -> tellAlg)

-- | The `writer` handler consumes `tell` operations, and
-- returns the final state @w@.
writer :: Monoid w => Handler '[Tell w] '[] '[W.WriterT w] a (w, a)
writer = handler' (fmap swap . W.runWriterT) (tellAlg :# emptyAlg)

-- | Staged version of `writer`.
writerC :: Monoid w => HandlerC '[Tell w] '[] '[W.WriterT w] a (w, a)
writerC = HandlerC
  (RunnerC $ \_ -> [|| fmap swap . W.runWriterT ||])
  (AlgTransC $ \_ -> [|| NT tellAlg ||] :#$ emptyAlgC)

-- | The `writer_` handler deals with `tell` operations, and
-- silently discards the final state.
writer_ :: Monoid w => Handler '[Tell w] '[] '[W.WriterT w] a a
writer_ = handler' (fmap fst . W.runWriterT) (tellAlg :# emptyAlg)

-- | Staged version of `writer_`.
writerC_ :: Monoid w => HandlerC '[Tell w] '[] '[W.WriterT w] a a
writerC_ = HandlerC
  (RunnerC $ \_ -> [|| fmap fst . W.runWriterT ||])
  (AlgTransC $ \_ -> [|| NT tellAlg ||] :#$ emptyAlgC)

-- | The `writerIO` handler translates `tell` operations to
-- physical IO printing.
writerIO :: Handler '[Tell String] '[Alg IO] '[] a a
writerIO = interpret1 $
  \(Tell w k) -> do io (putStr w)
                    return k

-- | Staged version of `writerIO`.
writerIOC :: HandlerC '[Tell String] '[Alg IO] '[] a a
writerIOC = interpretM1C $ \oalgc ->
  [|| NT $ \(Tell w k) -> do $$(callMC oalgc) (Alg (putStr w)); return k ||]

$(makeScp [e| censor :: forall w. (w -> w) ~> 1 |])
instance U.Unary (Censor_ w) where
  get (Censor_ c x) = x

-- | The `uncensors` handler removes any occurrences of `censor`.
uncensors :: forall w a . Handler '[Censor w] '[] '[] a a
uncensors = handler' id ((\(Censor (_ :: w -> w) k) -> k) :# emptyAlg)

-- | The @`censors` f@ handler applies an initial function @f@ to the
-- output produced by `tell`. If a @`censor` f' p@ operation is encountered,
-- @p@ will be censored by the composition @f . f'@, and the `censor` operation
-- will be consumed.
censors :: forall w a . (w -> w) -> Handler '[Tell w, Censor w] '[Tell w] '[ReaderT (w -> w)] a a
censors cipher = handler (\_ -> run) (getAT censorAT) where
  run :: (forall x. ReaderT (w -> w) m x -> m x)
  run (ReaderT mx) = mx cipher

-- | The algebra transformer underlying `censors`.
censorAT :: AlgTrans '[Tell w, Censor w] '[Tell w] '[ReaderT (w -> w)] Monad
censorAT = AlgTrans $ \oalg ->
  (\(Tell w k) -> do cipher <- ask; lift (callM oalg (Tell (cipher w) k))) :#.
  (\(Censor (cipher' :: w -> w) k) -> do cipher <- ask; lift (runReaderT k (cipher . cipher')))