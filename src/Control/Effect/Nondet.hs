{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Nondet where

import Prelude hiding (or)

import Control.Monad.Trans.Class ( MonadTrans(..) )
import Control.Effect
import Control.Monad.Trans.List
import Control.Applicative ( Alternative(empty, (<|>)) )


data Stop a where
  Stop :: Stop a
  deriving Functor

stop :: Members '[Stop] sig => Prog sig a
stop  = injCall (Alg Stop)

data Or a where
  Or :: a -> a -> Or a
  deriving Functor

or :: Members '[Or] sig => Prog sig a -> Prog sig a -> Prog sig a
or x y = injCall (Alg (Or x y))


instance (Members [Or, Stop] sig) => Alternative (Prog sig) where
  empty :: Members [Or, Stop] sig => Prog sig a
  empty = stop

  (<|>) :: Members [Or, Stop] sig => Prog sig a -> Prog sig a -> Prog sig a
  (<|>) = or

select :: Members [Or, Stop] sig => [a] -> Prog sig a
select = foldr (or . return) stop

nondetAlg
  :: (MonadTrans t, Alternative (t m) , Monad m)
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Stop , Or] (t m) x -> t m x)
nondetAlg oalg eff
  | Just (Alg Stop)     <- prj eff = empty
  | Just (Alg (Or x y)) <- prj eff = return x <|> return y

nondetFwd
  :: (Monad m)
  => (forall x. Effs sig m x -> m x)
  -> forall x. Effs sig (ListT m) x -> ListT m x
nondetFwd alg (Eff (Alg x)) = lift  (alg (Eff (Alg x)))
nondetFwd alg (Eff (Scp x)) = ListT (alg (Eff (Scp (fmap runListT x))))
nondetFwd alg (Effs effs)   = nondetFwd (alg . Effs) effs

nondet :: Handler [Stop, Or] '[] '[[]]
nondet = handler runListT' nondetAlg nondetFwd

-------------------------------
-- Example: Backtracking (and Culling?)
data Once a where
  Once :: a -> Once a
  deriving Functor

once
  :: Member Once sig => Prog sig a -> Prog sig a
once p = injCall (Scp (Once (fmap return p)))

-- Everything can be handled together. Here is the non-modular way
-- list :: (Member (Or) sig, Member (Stop) sig, Member (Once) sig) => Prog sig a -> [a]
list :: Prog [Stop, Or, Once] a -> [a]
list = eval halg where
  halg :: Effs [Stop, Or, Once] [] a -> [a]
  halg op
    | Just (Alg Stop)          <- prj op = []
    | Just (Alg (Or x y))      <- prj op = [x, y]
    | Just (Scp (Once []))     <- prj op = []
    | Just (Scp (Once (x:xs))) <- prj op = [x]

backtrackAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Stop, Or, Once] (ListT m) x -> ListT m x)
backtrackAlg oalg op
  | Just (Alg Stop)     <- prj op = empty
  | Just (Alg (Or x y)) <- prj op = return x <|> return y
  | Just (Scp (Once p)) <- prj op =
    ListT $ do mx <- runListT p
               case mx of
                 Nothing       -> return Nothing
                 Just (x, mxs) -> return (Just (x, empty))


backtrackOnceAlg
  :: Monad m
  => (forall x . oeff m x -> m x)
  -> (forall x . Effs '[Once] (ListT m) x -> ListT m x)
backtrackOnceAlg oalg op
  | Just (Scp (Once p)) <- prj op =
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


backtrackFwd
  :: (Monad m)
  => (forall x. Effs sig m x -> m x)
  -> forall x. Effs sig (ListT m) x -> ListT m x
backtrackFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
backtrackFwd alg (Eff (Scp x)) = ListT (alg (Eff (Scp (fmap runListT x))))
backtrackFwd alg (Effs effs)   = backtrackFwd (alg . Effs) effs

backtrack :: Handler [Stop, Or, Once] '[] '[[]]
backtrack = handler runListT' backtrackAlg' backtrackFwd
