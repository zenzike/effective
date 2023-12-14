{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Writer where
import Control.Effect
import Data.Tuple (swap)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Identity
import qualified Control.Monad.Trans.Writer as W
import Data.HFunctor
import Data.Functor.Composes (Comps(CNil))

data Tell w k where
  Tell :: w -> k -> Tell w k
  deriving Functor

tell :: (Monoid w) => w -> Prog' '[Tell w] ()
tell w = (Call . inj) (Alg (Tell w (return ())))

data Censor w k where
  Censor :: (w -> w) -> k -> Censor w k
  deriving Functor

censor :: Member (Censor w) sig => (w -> w) -> Prog sig a -> Prog sig a
censor cipher p = (Call . inj) (Scp (Censor cipher (fmap return p)))

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
