{-|
Module      : Control.Effect.Writer
Description : Effects for the writer monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}


module Control.Effect.Writer (
  -- * Syntax
  -- ** Operations

-- | The @`tell` w@ operation outputs @w@.
  tell,
  tellP,
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
  writerIO,
  censors,
  uncensors,

  -- ** Algebras
  writerAlg,
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
$(makeGen [e| tell :: forall w. w -> () |])

-- | The algebra transformer for the `writer` handler.
writerAT :: Monoid w => AlgTrans '[Tell w] '[] '[W.WriterT w] Monad
writerAT = AlgTrans writerAlg

-- | The algebra for the `writer` handler.
{-# INLINE writerAlg #-}
writerAlg
  :: (Monad m, Monoid w)
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs '[Tell w] (W.WriterT w m) x -> W.WriterT w m x)
writerAlg _ eff
  | Just (Alg (Tell_ w x)) <- prj eff =
      do W.tell w
         return x

-- | The `writer` handler consumes `tell` operations, and
-- returns the final state @w@.
writer :: Monoid w => Handler '[Tell w] '[] '[W.WriterT w] a (w, a)
writer = handler' (fmap swap . W.runWriterT) writerAlg

-- | The `writer_` handler deals with `tell` operations, and
-- silently discards the final state.
writer_ :: Monoid w => Handler '[Tell w] '[] '[W.WriterT w] a a
writer_ = handler' (fmap fst . W.runWriterT) writerAlg

-- | The `writerIO` handler translates `tell` operations to
-- physical IO printing.
writerIO :: Handler '[Tell String] '[Alg IO] '[] a a
writerIO = interpret $
  \(Tell w k) -> do io (putStr w)
                    return k

$(makeScp [e| censor :: forall w. (w -> w) -> 1 |])

instance U.Unary (Censor_ w) where
  get (Censor_ c x) = x

-- | The @`censors` f@ handler applies an initial function @f@ to the
-- any output produced by `tell`. If a @`censor` f' p@ operation is encountered,
-- @p@ will be censored by the composition @f . f'@, and the `censor` operation
-- will be consumed.
censors :: forall w a . (w -> w) -> Handler '[Tell w, Censor w] '[Tell w] '[ReaderT (w -> w)] a a
censors cipher = handler' run (getAT censorAT) where
  run :: Monad m => (forall x. ReaderT (w -> w) m x -> m x)
  run (ReaderT mx) = mx cipher

censorAT :: AlgTrans '[Tell w, Censor w] '[Tell w] '[ReaderT (w -> w)] Monad
censorAT = AlgTrans alg where
  alg :: Monad m
      => (forall x. Effs '[Tell w] m x -> m x)
      -> (forall x. Effs '[Tell w, Censor w] (ReaderT (w -> w) m) x -> ReaderT (w -> w) m x)
  alg oalg (Tell w k) = do
    cipher <- ask
    lift (oalg (Eff (Alg (Tell_ (cipher w) k))))
  alg oalg (Censor (cipher' :: w -> w) k) = do
    cipher <- ask
    lift (runReaderT k (cipher . cipher'))

-- | The `uncensors` handler removes any occurrences of `censor`.
uncensors :: forall w a . Handler '[Censor w] '[] '[] a a
uncensors = handler' id (\_ (Censor (_ :: w -> w) k) -> k) where
