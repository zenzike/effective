{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Writer where
import Control.Effect
import Data.Tuple (swap)
import Control.Family.AlgScp
import Control.Handler
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Identity
import qualified Control.Monad.Trans.Writer as W
import Data.HFunctor


data Tell' w k where
  Tell :: w -> k -> Tell' w k
  deriving Functor

type Tell w = Algebraic (Tell' w)

tell :: Monoid w => w -> Prog' '[Tell w] ()
tell w = (Call . inj) (Algebraic (Tell w (return ())))

data Censor' w k where
  Censor :: (w -> w) -> k -> Censor' w k
  deriving Functor

type Censor w = Scoped (Censor' w)

censor :: Member (Censor w) sig => (w -> w) -> Prog sig a -> Prog sig a
censor cipher p = injCall (Scoped (Censor cipher (fmap return p)))

-- Amazingly this handler can forward operations from any family.
censors :: forall w fam . Monoid w => (w -> w) -> Handler '[Tell w, Censor w] '[Tell w, Censor w] '[] fam
censors cipher = handler run alg fwd where
  run :: Monad m
      => (forall x. Effs '[Tell w, Censor w] m x -> m x)
      -> (forall x. ReaderT (w -> w) m x -> m x)
  run oalg (ReaderT mx) = mx cipher

  alg :: Monad m
      => (forall x. Effs '[Tell w, Censor w] m x -> m x)
      -> (forall x. Effs '[Tell w, Censor w] (ReaderT (w -> w) m) x -> ReaderT (w -> w) m x)
  alg oalg eff
    | Just (Algebraic (Tell w k)) <- prj eff =
        do cipher <- ask
           lift (oalg (Eff (Algebraic (Tell (cipher w) k))))
    | Just (Scoped (Censor (cipher' :: w -> w) k)) <- prj eff =
        do cipher <- ask
           lift (oalg (Effs (Eff (Scoped (Censor cipher' (runReaderT k (cipher . cipher')))))))

  fwd :: (Monad m, HFunctor sig)
      => (forall x. sig m x -> m x)
      -> (forall x. sig (ReaderT (w -> w) m) x -> ReaderT (w -> w) m x)
  fwd oalg c = ReaderT (\f -> oalg $ hmap (flip runReaderT f) c)

uncensors :: forall w fam . Monoid w => Handler '[Censor w] '[] '[] fam
uncensors = handler run alg fwd where
  run :: Monad m
      => (forall x. Effs '[] m x -> m x)
      -> (forall x. IdentityT m x -> m x)
  run oalg = runIdentityT 

  alg :: Monad m
      => (forall x. Effs '[] m x -> m x)
      -> (forall x. Effs '[Censor w] (IdentityT m) x -> IdentityT m x)
  alg oalg (Eff (Scoped (Censor (_ :: w -> w) k))) = k

  fwd :: (Monad m, HFunctor sig)
      => (forall x. sig m x -> m x)
      -> (forall x. sig (IdentityT m) x -> IdentityT m x)
  fwd oalg c = IdentityT (oalg $ hmap runIdentityT c)

writerAlg
  :: (Monad m, Monoid w)
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs '[Tell w, Censor w] (W.WriterT w m) x -> W.WriterT w m x)
writerAlg _ eff
  | Just (Algebraic (Tell w k)) <- prj eff =
      do W.tell w
         return k
  | Just (Scoped (Censor f p)) <- prj eff =
      do W.censor f p

writerFwd
  :: (Monad m, Monoid w, Functor lsig)
  => (forall x. lsig (m x) -> m x)
  -> (forall x. lsig (W.WriterT w m x) -> W.WriterT w m x)

writerFwd alg x = W.WriterT (alg (fmap W.runWriterT x))

writer :: Monoid w => ASHandler '[Tell w, Censor w] '[] '[(,) w]
writer = ashandler (\_ -> fmap swap . W.runWriterT) writerAlg writerFwd

writer_ :: Monoid w =>ASHandler '[Tell w, Censor w] '[] '[]
writer_ = ashandler (\_ -> fmap fst . W.runWriterT) writerAlg writerFwd
