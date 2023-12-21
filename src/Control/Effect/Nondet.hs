{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Nondet where

import Prelude hiding (or)

import Data.HFunctor ( HFunctor(..) )

import Control.Effect
import Control.Handler
import Control.Family.AlgScp
import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad ( ap, liftM )
import Control.Monad.Trans.Class ( MonadTrans(..) )
import Control.Arrow ( Arrow(second) )


data Stop' a where
  Stop :: Stop' a
  deriving Functor

type Stop = Algebraic Stop'

stop :: Members '[Stop] sig => Prog sig a
stop  = injCall (Algebraic Stop)

data Or' a where
  Or :: a -> a -> Or' a
  deriving Functor

type Or = Algebraic Or'

or :: Members '[Or] sig => Prog sig a -> Prog sig a -> Prog sig a
or x y = injCall (Algebraic (Or x y))


instance (Members [Or, Stop] sig) => Alternative (Prog sig) where
  empty :: Members [Or, Stop] sig => Prog sig a
  empty = stop

  (<|>) :: Members [Or, Stop] sig => Prog sig a -> Prog sig a -> Prog sig a
  (<|>) = or


select :: Members [Or, Stop] sig => [a] -> Prog sig a
select = foldr (or . return) stop

newtype ListT m a = ListT { runListT :: m (Maybe (a, ListT m a)) }
  deriving Functor

runListT' :: Monad m => ListT m a -> m [a]
runListT' (ListT mmxs) =
  do mxs <- mmxs
     case mxs of
       Nothing         -> return []
       Just (x, mmxs') -> (x :) <$> runListT' mmxs'

instance HFunctor ListT where
  hmap :: (Functor f, Functor g) => (forall x1. f x1 -> g x1) -> ListT f x -> ListT g x
  hmap h (ListT mx) = ListT (fmap (fmap (fmap (hmap h))) (h mx))

foldListT :: Monad m => (a -> m b -> m b) -> m b -> ListT m a -> m b
foldListT k ys (ListT mxs) = mxs >>= maybe ys (\(x,xs) -> k x (foldListT k ys xs))

instance Monad m => Applicative (ListT m) where
  pure x = ListT (pure (Just (x, empty)))
  (<*>) = ap

instance Monad m => Monad (ListT m) where
  (>>=) :: Monad m => ListT m a -> (a -> ListT m b) -> ListT m b
  m >>= f = ListT $ foldListT (\x l -> runListT $ f x <|> ListT l) (return Nothing) m

instance Monad m => Alternative (ListT m) where
  empty = ListT (return Nothing)
  (<|>) :: Monad m => ListT m a -> ListT m a -> ListT m a
  ListT mxs <|> ListT mys = ListT $
    mxs >>= maybe mys (return . Just . second (<|> ListT mys))

instance MonadTrans ListT where
  lift :: Monad m => m a -> ListT m a
  lift = ListT . liftM (\x -> Just (x, empty))

nondetAlg
  :: (MonadTrans t, Alternative (t m) , Monad m)
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Stop , Or] (t m) x -> t m x)
nondetAlg oalg eff
  | Just (Algebraic Stop)     <- prj eff = empty
  | Just (Algebraic (Or x y)) <- prj eff = return x <|> return y

nondetFwd
  :: (Monad m, Functor lsig)
  => (forall x. lsig (m x) -> m x)
  -> forall x. lsig (ListT m x) -> ListT m x
nondetFwd alg x = ListT (alg (fmap runListT x))

nondet :: ASHandler [Stop, Or] '[] '[[]]
nondet = ashandler (\_ -> runListT') nondetAlg nondetFwd


-------------------------------
-- Example: Backtracking (and Culling?)
data Once' a where
  Once :: a -> Once' a
  deriving Functor

type Once = Scoped Once'

once
  :: Member Once sig => Prog sig a -> Prog sig a
once p = injCall (Scoped (Once (fmap return p)))

-- Everything can be handled together. Here is the non-modular way
-- list :: (Member (Or) sig, Member (Stop) sig, Member (Once) sig) => Prog sig a -> [a]
list :: Prog [Stop, Or, Once] a -> [a]
list = eval halg where
  halg :: Effs [Stop, Or, Once] [] a -> [a]
  halg op
    | Just (Algebraic Stop)          <- prj op = []
    | Just (Algebraic (Or x y))      <- prj op = [x, y]
    | Just (Scoped (Once []))        <- prj op = []
    | Just (Scoped (Once (x:xs)))    <- prj op = [x]

backtrackAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Stop, Or, Once] (ListT m) x -> ListT m x)
backtrackAlg oalg op
  | Just (Algebraic Stop)     <- prj op = empty
  | Just (Algebraic (Or x y)) <- prj op = return x <|> return y
  | Just (Scoped (Once p))    <- prj op =
    ListT $ do mx <- runListT p
               case mx of
                 Nothing       -> return Nothing
                 Just (x, mxs) -> return (Just (x, empty))


backtrackOnceAlg
  :: Monad m
  => (forall x . oeff m x -> m x)
  -> (forall x . Effs '[Once] (ListT m) x -> ListT m x)
backtrackOnceAlg oalg op
  | Just (Scoped (Once p)) <- prj op =
    ListT $ do mx <- runListT p
               case mx of
                 Nothing       -> return Nothing
                 Just (x, mxs) -> return (Just (x, empty))

backtrackAlg'
  :: Monad m => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Stop, Or, Once] (ListT m) x -> ListT m x)
backtrackAlg' = joinAlg nondetAlg backtrackOnceAlg
-- TODO: The alternative with monad transformers is painful.
-- TODO: this becomes interesting when different search strategies are used

backtrack :: ASHandler [Stop, Or, Once] '[] '[[]]
backtrack = ashandler (\_ -> runListT') backtrackAlg' nondetFwd

