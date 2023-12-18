{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.State where
import Control.Family.AlgScp
import Control.Handler
import Control.Effect.MCarrier
import Data.EitherF

import Data.Tuple (swap)

import Data.Functor.Identity
import Control.Effects
import qualified Control.Monad.Trans.State.Lazy as S

data Put' s k where
  Put :: s -> k -> Put' s k
  deriving Functor

data Get' s k where
  Get :: (s -> k) -> Get' s k
  deriving Functor

type Put s = Algebraic (Put' s)
type Get s = Algebraic (Get' s)
type State s = '[Put s, Get s]

put :: Member (Put s) sig => s -> Prog sig ()
put s = (Call . inj) (Algebraic (Put s (return ())))

get :: Member (Get s) sig => Prog sig s
get = injCall (Algebraic (Get return))

stateAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put s, Get s] (S.StateT s m) x -> S.StateT s m x)
stateAlg _ eff
  | Just (Algebraic (Put s p)) <- prj eff =
      do S.put s
         return p
  | Just (Algebraic (Get p)) <- prj eff =
      do s <- S.get
         return (p s)
-- Although the type safe way to write stateAlg is the following
--   stateAlg' _ (Eff (Algebraic (Put s p))) = ...
--   stateAlg' _ (Effs (Eff (Algebraic (Get p)))) = ...
-- the way above using view pattern looks nicer (at the cost of pattern-match
-- totality checking).

stateFwd
  :: (Monad m, Functor lsig)
  => (forall x. lsig (m x) -> m x)
  -> (forall x. lsig (S.StateT s m x) -> S.StateT s m x)
stateFwd alg x = S.StateT (\s -> alg (fmap (flip S.runStateT s) x))

state :: s -> ASHandler [Put s, Get s] '[] '[((,) s)]
state s = ashandler (\_ x -> fmap swap (S.runStateT x s)) stateAlg stateFwd

-- | The `state_` handler deals with stateful operations and silenty
-- discards the final state.
state_ :: s -> ASHandler [Put s, Get s] '[] '[]
state_ s = ashandler (\_ x -> fmap fst (S.runStateT x s)) stateAlg stateFwd


-- The `StateC` carrier is not a monad, and this code shows how it can
-- nevertheless be used to create a `MCarrier`, which then generates a
-- modular handler using continuation monad transformation. However, the
-- resulting modular handler only forwards algebraic operations, so it is
-- less useful than `state` defined above.
data StateC s m x = StateC { runStateC :: s -> m x }

stateC :: forall s . s -> MCarrier (StateC s) Identity (EitherF (Get' s) (Put' s))
stateC s = MCarrier crun calg cfwd cgen where
  cfwd :: forall m x . Monad m => m (StateC s m x) -> StateC s m x
  cfwd mx = StateC $ \s -> do x <- mx
                              runStateC x s

  calg :: forall m x . Monad m
    => EitherF (Get' s) (Put' s) (StateC s m x)
    -> StateC s m x
  calg (InlF (Get (k :: s -> StateC s m x))) = StateC (\s -> runStateC (k s) s)
  calg (InrF (Put (s' :: s) k)) = StateC (\s -> runStateC k s')

  crun :: forall m x . Monad m => StateC s m x -> m (Identity x)
  crun (StateC k) = fmap Identity (k s)

  cgen :: forall m x . Monad m => x -> StateC s m x
  cgen x = StateC (\s -> return x)

state_' :: s -> Handler' '[Algebraic (EitherF (Get' s) (Put' s))]
                         '[] 
                         (ContC (StateC s)) 
                         '[Identity] 
                         AlgFam
state_' s = convert (stateC s)
