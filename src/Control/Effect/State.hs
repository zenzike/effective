{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}

module Control.Effect.State where
import Control.Monad.Trans.Class (MonadTrans, lift)
import Control.Monad (join)
import Data.Tuple (swap)

import Control.Effect
import Data.HFunctor ( HFunctor(..) )
import qualified Control.Monad.Trans.State.Lazy as S

data Put s k where
  Put :: s -> k -> Put s k
  deriving Functor

data Get s k where
  Get :: (s -> k) -> Get s k
  deriving Functor

data Local s x where
  Local :: s -> x -> Local s x
  deriving Functor

type State s = '[Put s, Get s, Local s]

put'
  :: (Member (Put s) sig, Monad m)
  => (?oalg :: Effs sig m (m ()) -> m (m ()))
  => s -> m ()
put' s = (join . ?oalg . inj) (Alg (Put s (return ())))

put :: Member (Put s) sig => s -> Prog sig ()
put = put' where ?oalg = Call . fmap return
-- put s = injCall (Alg (Put s (return ())))

get' :: (Member (Get s) sig, Monad m)
  => (?oalg :: Effs sig m (m s) -> m (m s))
  => m s
get' = (join . ?oalg . inj) (Alg (Get return))


get :: Member (Get s) sig => Prog sig s
get = get' where ?oalg = Call . fmap return
-- get = injCall (Alg (Get return))

local :: Member (Local s) sig => s -> Prog sig a -> Prog sig a
local s p = injCall (Scp (Local s (fmap return p)))


instance HFunctor (S.StateT s) where
  hmap h (S.StateT p) = S.StateT (\s -> h (p s))

stateAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put s, Get s, Local s] (S.StateT s m) x -> S.StateT s m x)
stateAlg oalg eff
  | Just (Alg (Put s p)) <- prj eff =
      do S.put s
         return p
  | Just (Alg (Get p)) <- prj eff =
      do s <- S.get
         return (p s)
  | Just (Scp (Local s (S.StateT p))) <- prj eff =
      lift (fmap fst (p s))

stateFwd
  :: Monad m
  => (forall x. Effs sig m x -> m x)
  -> (forall x. Effs sig (S.StateT s m) x -> S.StateT s m x)
stateFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
stateFwd alg (Eff (Scp x)) = S.StateT (\s -> (alg (Eff (Scp (fmap (flip S.runStateT s) x)))))
stateFwd alg (Effs effs)   = stateFwd (alg . Effs) effs

state :: s -> Handler [Put s, Get s, Local s] '[S.StateT s] '[((,) s)] oeff
state s = handler (fmap swap . flip S.runStateT s) stateAlg stateFwd

