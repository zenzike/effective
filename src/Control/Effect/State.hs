{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.State where
import Control.Monad.Trans.Class (lift)
import Data.Tuple (swap)

import Data.Functor.Identity
import Control.Effect
import Data.Functor.Composes
import qualified Control.Monad.Trans.State.Lazy as S

data Put s k where
  Put :: s -> k -> Put s k
  deriving Functor

data Get s k where
  Get :: (s -> k) -> Get s k
  deriving Functor



type State s = '[Put s, Get s]

put :: Member (Put s) sig => s -> Prog sig ()
put s = (Call . inj) (Alg (Put s (return ())))

get :: Member (Get s) sig => Prog sig s
get = injCall (Alg (Get return))

stateAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put s, Get s] (S.StateT s m) x -> S.StateT s m x)
stateAlg _ eff
  | Just (Alg (Put s p)) <- prj eff =
      do S.put s
         return p
  | Just (Alg (Get p)) <- prj eff =
      do s <- S.get
         return (p s)

stateFwd
  :: Monad m
  => (forall x. Effs sig m x -> m x)
  -> (forall x. Effs sig (S.StateT s m) x -> S.StateT s m x)
stateFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
stateFwd alg (Eff (Scp x)) = S.StateT (\s -> (alg (Eff (Scp (fmap (flip S.runStateT s) x)))))
stateFwd alg (Effs effs)   = stateFwd (alg . Effs) effs

state :: s -> Handler [Put s, Get s] '[] '[((,) s)]
state s = handler (fmap swap . flip S.runStateT s) stateAlg stateFwd

-- | The `state_` handler deals with stateful operations and silenty
-- discards the final state.
state_ :: s -> Handler [Put s, Get s] '[] '[]
state_ s = Handler $ Handler' (\oalg -> fmap (CNil . fst) . flip S.runStateT s) stateAlg stateFwd

-- The `StateC` carrier is not a monad, and this code shows how it can
-- nevertheless be used to create a `Carrier`. In particular, the modular
-- handler that arises does not forward a scoped operation. No runtime error
-- should happen here, but this is not tracked by the type system.
data StateC s m x = StateC { runStateC :: s -> m x }

stateC :: forall s . s -> Carrier (StateC s) Identity '[Get s, Put s]
stateC s = Carrier cfwd calg crun cgen where
  cfwd :: forall m x . Monad m => m (StateC s m x) -> StateC s m x
  cfwd mx = StateC $ \s -> do x <- mx
                              runStateC x s

  calg :: forall m x . Monad m
    => Effs '[Get s, Put s] Identity (StateC s m x)
    -> StateC s m x
  calg eff
    | Just (Alg (Get (k :: s -> StateC s m x))) <- prj eff =
        StateC (\s -> runStateC (k s) s)
    | Just (Alg (Put (s' :: s) k)) <- prj eff =
        StateC (\s -> runStateC k s')

  crun :: forall m x . Monad m => StateC s m x -> m (Identity x)
  crun (StateC k) = fmap Identity (k s)

  cgen :: forall m x . Monad m => x -> StateC s m x
  cgen x = StateC (\s -> return x)

