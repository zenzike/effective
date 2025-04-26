{-|
Module      : Control.Effect.Writer
Description : Effects for the writer monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Writer (
  -- * Syntax
  -- ** Operations
  tell,
  censor,

  -- ** Signatures
  Tell, Tell_(..),
  Censor, Censor_(..),

  -- * Semantics
  -- ** Handlers
  writer,
  writer_,
  writerIO,
  censors,
  uncensors,

  -- ** Algebras
  writerAlg,
  writeAT,
  censorAT,

  -- ** Underlying monad transformers
  W.WriterT(..)
) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.IO (liftIO)

import qualified Data.Functor.Unary as U
import Data.Tuple (swap)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.Writer as W

-- | Signature for `tell`.
type Tell w = Alg (Tell_ w)
-- | Underlying signature for `tell`.
data Tell_ w k where
  Tell :: w -> k -> Tell_ w k
  deriving Functor

-- | @`tell` w@ produces the output @w@.
tell :: (Member (Tell w) sig, Monoid w) => w -> Prog sig ()
tell w = call (Alg (Tell w (return ())))

-- | The algebra transformer for the `writer` handler.
writeAT :: Monoid w => AlgTransM '[Tell w] '[] '[W.WriterT w]
writeAT = AlgTrans writerAlg

writerAlg
  :: (Monad m, Monoid w)
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs '[Tell w] (W.WriterT w m) x -> W.WriterT w m x)
writerAlg _ eff
  | Just (Alg (Tell w x)) <- prj eff =
      do W.tell w
         return x

-- | The `writer` handler consumes `tell` operations, and
-- returns the final state @w@.
writer :: Monoid w => Handler '[Tell w] '[] '[W.WriterT w] '[(,) w]
writer = handler' (fmap swap . W.runWriterT) writerAlg

-- | The `writer_` handler deals with `tell` operations, and
-- silently discards the final state.
writer_ :: Monoid w => Handler '[Tell w] '[] '[W.WriterT w] '[]
writer_ = handler' (fmap fst . W.runWriterT) writerAlg

-- | The `writerIO` handler translates `tell` operations to 
-- physical IO printing.
writerIO :: Handler '[Tell String] '[Alg IO] '[] '[]
writerIO = interpret $
  \(Eff (Alg (Tell w k))) -> do liftIO (putStr w)
                                return k

-- | Signature for 'censor'.
type Censor w = Scp (Censor_ w)
-- | Underlying signature for 'censor'.
data Censor_ w k where
  Censor :: (w -> w) -> k -> Censor_ w k
  deriving Functor

instance U.Unary (Censor_ w) where
  get (Censor c x) = x

-- | The @`censor` f p@ operation executes program @p@ with output censored
-- by @f@.
censor :: Member (Censor w) sig => (w -> w) -> Prog sig a -> Prog sig a
censor cipher p = call (Scp (Censor cipher (fmap return p)))

-- | The @`censors` f@ handler applies an initial function @f@ to the
-- any output produced by `tell`. If a @`censor` f' p@ operation is encountered,
-- @p@ will be censored by the composition @f . f'@, and the `censor` operation
-- will be consumed.
censors :: forall w . (w -> w) -> Handler '[Tell w, Censor w] '[Tell w] '[ReaderT (w -> w)] '[]
censors cipher = handler' run (getAT censorAT) where
  run :: Monad m => (forall x. ReaderT (w -> w) m x -> m x)
  run (ReaderT mx) = mx cipher

censorAT :: AlgTransM '[Tell w, Censor w] '[Tell w] '[ReaderT (w -> w)]
censorAT = AlgTrans alg where
  alg :: Monad m
      => (forall x. Effs '[Tell w] m x -> m x)
      -> (forall x. Effs '[Tell w, Censor w] (ReaderT (w -> w) m) x -> ReaderT (w -> w) m x)
  alg oalg eff
    | Just (Alg (Tell w k)) <- prj eff =
        do cipher <- ask
           lift (oalg (Eff (Alg (Tell (cipher w) k))))
    | Just (Scp (Censor (cipher' :: w -> w) k)) <- prj eff =
        do cipher <- ask
           lift (runReaderT k (cipher . cipher'))

-- | The `uncensors` handler removes any occurrences of `censor`.
uncensors :: forall w . Handler '[Censor w] '[] '[] '[]
uncensors = handler' id alg where
  alg :: Monad m
      => (forall x. Effs '[] m x -> m x)
      -> (forall x. Effs '[Censor w] m x -> m x)
  alg oalg (Eff (Scp (Censor (_ :: w -> w) k))) = k
