{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Nondet where

import Prelude hiding (or)

import Control.Monad.Trans.Class ( MonadTrans(..) )
import Control.Effect
import Control.Monad.Trans.List ( runListT', ListT(..) )
import Control.Monad.Trans.State ( StateT(..), withStateT, get, put  )
import Control.Handler
import Control.Family.AlgScp
import Control.Family
import Control.Family.Algebraic
import Control.Applicative ( Alternative(empty, (<|>)) )


data Nat a = Nat Int a

data Stop' a where
  Stop :: Stop' a
  deriving (Functor, Show)

-- data Stop f a where
--   Stop :: Stop f a 
--   deriving (AlgebraicOps, ...)

type Stop = Algebraic Stop'

data instance FAM Stop' = Algebraic

stop :: Members '[Stop] sig => Prog sig a
stop  = injCall (Algebraic Stop)

data Or' a where
  Or :: a -> a -> Or' a
  deriving (Functor, Show)

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

selects :: [a] -> Prog' [Or, Stop] (a, [a])
selects []      =  empty
selects (x:xs)  =  return (x, xs)  <|>  do  (y, ys) <- selects xs
                                            return (y, x:ys)

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
  deriving (Functor, Show)

type Once = Scoped Once'

once
  :: Member Once sig => Prog sig a -> Prog sig a
once p = injCall (Scoped (Once (fmap return p)))

data Search' a where
  Search :: a -> Search' a
  deriving Functor

type Search = Scoped Search'

search :: Member Search sig => Prog sig a -> Prog sig a
search p = injCall (Scoped (Search (fmap return p)))

data Depth' a where
  Depth :: Int -> a -> Depth' a
  deriving Functor

type Depth = Scoped Depth'

depth :: Member Depth sig => Int -> Prog sig a -> Prog sig a
depth d p = injCall (Scoped (Depth d (fmap return p)))

data DBS' a where
  DBS :: Int -> a -> DBS' a
  deriving Functor

type DBS = Scoped DBS'

dbs :: Member DBS sig => Int -> Prog sig a -> Prog sig a
dbs d p = injCall (Scoped (DBS d (fmap return p)))

-- searchOnce :: Handler '[Search] '[Once] '[]
-- searchOnce = interpret undefined

-- searchWith strategy = interpret ... strategy ...

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

-- backtrackDepthAlg
--   :: Monad m
--   => (forall x . oeff m x -> m x)
--   -> (forall x . Effs '[Stop, Or, Depth] (ReaderT Int (ListT m)) x -> ReaderT Int (ListT m) x)
-- backtrackDepthAlg oalg op
--   | Just (Alg Stop)        <- prj op = ReaderT (const empty)
--   | Just (Alg (Or x y))    <- prj op = ReaderT (\d -> if d == 0
--                                                         then empty
--                                                         else _)
--   | Just (Scp (Depth d p)) <- prj op =
--       ReaderT (\d' -> ListT (do mx <- runListT (runReaderT p d)
--                                 case mx of
--                                   Nothing       -> return Nothing
--                                   Just (x, mxs) -> return (Just (x, mxs))
--       ))

backtrackDepthAlg
  :: Monad m
  => (forall x . oeff m x -> m x)
  -> (forall x . Effs '[Stop, Or, Depth] (StateT Int (ListT m)) x -> StateT Int (ListT m) x)
backtrackDepthAlg oalg op
  | Just (Algebraic Stop)     <- prj op = empty
  | Just (Algebraic (Or x y)) <- prj op =
      do d <- get
         if d == 0
           then empty
           else (put (d - 1) >> pure x) <|> (put (d - 1) >> pure y)
  | Just (Scoped (Depth d p)) <- prj op = withStateT (const d) p
backtrack :: ASHandler [Stop, Or, Once] '[] '[[]]
backtrack = ashandler (\_ -> runListT') backtrackAlg' nondetFwd



-- searchWith :: Handler '[Stop, Or, Once, Search] '[] '[[]]
-- searchWith = handler runListT' backtrackAlg' backtrackFwd

instance Fam Stop' where
  type FLower Stop' = Algebraic Stop'

