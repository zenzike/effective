{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Writer where
import Control.Effect
import Data.Tuple (swap)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Identity
import qualified Control.Monad.Trans.Writer as W
import Data.HFunctor
import Data.Functor.Composes (Comps(CNil))

import Control.Monad.Writer.Class

data Tell w k where
  Tell :: w -> k -> Tell w k
  deriving Functor

-- instance (Monoid w, MonadProg (Tell w ': sigs) m) => MonadWriter w m where
--   tell w = (call . inj) (Alg (Tell w (return ())))

-- TODO: I think that this needs better testing. Maybe it should
-- fail to unify sig without the Members contraint
-- tell :: (Member (Tell w) effs, Monoid w) => w -> Prog effs ()
tell :: (Monoid w) => w -> Prog' '[Tell w] ()
tell w = (Call . inj) (Alg (Tell w (return ())))

-- tell :: forall w m effs . (Members '[Tell w] effs, MonadProg effs m, Monoid w) 
--   => w -> m ()
-- tell w = (call . inj) (Alg (Tell w (return ())))




-- instance MonadProg () where

data Censor w k where
  Censor :: (w -> w) -> k -> Censor w k
  deriving Functor

censor :: Member (Censor w) sig => (w -> w) -> Prog sig a -> Prog sig a
censor cipher p = (Call . inj) (Scp (Censor cipher (fmap return p)))

-- NOTE: this cannot be done as the fusion of `censorsTell` and `censorsCensor`,
-- since `tell` must be sensitive to any encapsulating `censor`.
censors :: forall w . Monoid w => (w -> w) -> Handler '[Tell w, Censor w] '[Tell w, Censor w] '[]
censors cipher = Handler $ Handler' run alg fwd where
  run :: Monad m
      => (forall x. Effs '[Tell w, Censor w] m x -> m x)
      -> (forall x. ReaderT (w -> w) m x -> m (Comps '[] x))
  run oalg (ReaderT mx) = fmap CNil (mx cipher)

  alg :: Monad m
      => (forall x. Effs '[Tell w, Censor w] m x -> m x)
      -> (forall x. Effs '[Tell w, Censor w] (ReaderT (w -> w) m) x -> ReaderT (w -> w) m x)
  alg oalg eff
    | Just (Alg (Tell w k)) <- prj eff =
        do cipher <- ask
           lift (oalg (Eff (Alg (Tell (cipher w) k))))
    | Just (Scp (Censor (cipher' :: w -> w) k)) <- prj eff =
        do cipher <- ask
           lift (oalg (Effs (Eff (Scp (Censor cipher' (runReaderT k (cipher . cipher')))))))

  fwd :: Monad m
      => (forall x. Effs sig m x -> m x)
      -> (forall x. Effs sig (ReaderT (w -> w) m) x -> ReaderT (w -> w) m x)
  fwd oalg c = ReaderT (\f -> oalg $ hmap (flip runReaderT f) c)

censors' :: forall w . Monoid w => (w -> w) -> Handler '[Tell w, Censor w] '[Tell w] '[]
censors' cipher = Handler $ Handler' run alg fwd where
  run :: Monad m
      => (forall x. Effs '[Tell w] m x -> m x)
      -> (forall x. ReaderT (w -> w) m x -> m (Comps '[] x))
  run oalg (ReaderT mx) = fmap CNil (mx cipher)

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
           -- lift (oalg (Effs (Eff (Scp (Censor cipher' (runReaderT k (cipher . cipher')))))))

  fwd :: Monad m
      => (forall x. Effs sig m x -> m x)
      -> (forall x. Effs sig (ReaderT (w -> w) m) x -> ReaderT (w -> w) m x)
  fwd oalg c = ReaderT (\f -> oalg $ hmap (flip runReaderT f) c)

-- This should be equivalent to:
--   uncensors = hide @'[Censors w] (writer @w) <&> writer @w
-- uncensors :: forall w . Monoid w => Handler '[Tell w, Censor w] '[Tell w] '[]
-- uncensors = Handler $ Handler' run alg fwd where
--   run :: Monad m
--       => (forall x. Effs '[Tell w] m x -> m x)
--       -> (forall x. IdentityT m x -> m (Comps '[] x))
--   run oalg (IdentityT mx) = fmap CNil (mx)
--
--   alg :: Monad m
--       => (forall x. Effs '[Tell w] m x -> m x)
--       -> (forall x. Effs '[Tell w, Censor w] (IdentityT m) x -> IdentityT m x)
--   alg oalg eff
--     | Just (Alg (Tell w k)) <- prj eff =
--         lift (oalg (Eff (Alg (Tell w k))))
--     | Just (Scp (Censor (_ :: w -> w) k)) <- prj eff =
--         k
--
--   fwd :: Monad m
--       => (forall x. Effs sig m x -> m x)
--       -> (forall x. Effs sig (IdentityT m) x -> IdentityT m x)
--   fwd oalg c = IdentityT (oalg $ hmap runIdentityT c)

uncensors :: forall w . Monoid w => Handler '[Censor w] '[] '[]
uncensors = Handler $ Handler' run alg fwd where
  run :: Monad m
      => (forall x. Effs '[] m x -> m x)
      -> (forall x. IdentityT m x -> m (Comps '[] x))
  run oalg (IdentityT mx) = fmap CNil (mx)

  alg :: Monad m
      => (forall x. Effs '[] m x -> m x)
      -> (forall x. Effs '[Censor w] (IdentityT m) x -> IdentityT m x)
  alg oalg (Eff (Scp (Censor (_ :: w -> w) k))) = k

  fwd :: Monad m
      => (forall x. Effs sig m x -> m x)
      -> (forall x. Effs sig (IdentityT m) x -> IdentityT m x)
  fwd oalg c = IdentityT (oalg $ hmap runIdentityT c)

writerAlg
  :: (Monad m, Monoid w)
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs '[Tell w, Censor w] (W.WriterT w m) x -> W.WriterT w m x)
writerAlg _ eff
  | Just (Alg (Tell w k)) <- prj eff =
      do W.tell w
         return k
  | Just (Scp (Censor f p)) <- prj eff =
      do W.censor f p

writerFwd
  :: (Monad m, Monoid w)
  => (forall x. Effs sig m x -> m x)
  -> (forall x. Effs sig (W.WriterT w m) x -> W.WriterT w m x)
writerFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
writerFwd alg (Eff (Scp x)) = W.WriterT (alg (Eff (Scp (fmap W.runWriterT x))))
writerFwd alg (Effs effs)   = writerFwd (alg . Effs) effs

writer :: Monoid w => Handler '[Tell w, Censor w] '[] '[(,) w]
writer = handler (fmap swap . W.runWriterT) writerAlg writerFwd

writer_ :: Monoid w => Handler '[Tell w, Censor w] '[] '[]
writer_ = Handler $ Handler' (\oalg -> fmap (CNil . fst) . W.runWriterT) writerAlg writerFwd
