{-|
Module      : Control.Effect.Distributive
Description : The distributive effect family
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

Distributive effects on a monad @m@ are operations of the form 
@forall x. r (m x) -> r (m x)@ for functors @r@, which are isomorphic to 
functions of type @forall x. (exists b. (r (m b) , r b -> a)) -> r x@ by
left Kan extension. A good example of operations in this form is
@jpar :: forall x. (m x, m x) -> m (x, x)@ that runs two computations
in paralell and wait until both of them finish (this is in contrast from
the operation @par :: forall x. (m x, m x) -> m x@ from "Control.Effect.Distributive", 
which only keeps the result from the first computation). 

These operations were called \'parallel effects\' in the paper "A framework for
higher-order effects & handlers" by Birthe van den Berg and Tom Schrijvers, but
they are not inherently tied to parallel composition, so we call them
distributive effects in this library, since such operations @forall x. r (m x) -> r (m x)@
are called /distributive laws/ (between functors @r@ and @m@) and are well
studied in theoretical computer science (distributive laws between
around the powerset functor and probabilistic distribution monad are especially
important in the study of (nondeterministic/probabilistic) automata theory.)
-}

module Control.Effect.Distributive where

import Data.Kind ( Type )
import Data.HFunctor
import Control.Effect

import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader

data Distr (r :: Type -> Type) (f :: Type -> Type) a where
  Distr :: r (f b) -> (r b -> a) -> Distr r f a

-- | An operation @op : forall x. Distr r f x -> f x@ on a functor @f@ accepts
-- @r@-many @f@-computations (@r (f b)@) and a \'combiner function\' @r b -> a@,
-- and produces an @f@-computation of @a@. These operations are in bijection
-- with distributive laws `forall a. r (f a) -> f (r a)`, exhibited by the
-- functions @distrOp@ and @opDistr@.

distrOp :: (forall a. Distr r f a -> f a)
      -> (forall a. r (f a) -> f (r a))
distrOp op rf = op (Distr rf id)

opDistr :: Functor f 
         => (forall a. r (f a) -> f (r a))
         -> (forall a. Distr r f a -> f a)
opDistr d (Distr rf c) = fmap c (d rf) 

instance Functor r => Functor (Distr r f) where
  fmap f (Distr p c) = Distr p (f . c)

instance Functor r => HFunctor (Distr r) where
  hmap h (Distr p c) = Distr (fmap h p) c

instance Functor r => Forward (Distr r) IdentityT where
  fwd oalg (Distr p c) = IdentityT (oalg (Distr (fmap runIdentityT p) c))

instance Traversable r => Forward (Distr r) MaybeT where
  -- | We actually only need `sequenceA` between `r` and `Maybe`.
  fwd oalg (Distr p c) = MaybeT $ oalg (Distr (fmap runMaybeT p) c') where
    c' = fmap c . sequenceA

instance Traversable r => Forward (Distr r) (ExceptT e) where
  -- | We actually only need `sequenceA` between `r` and `Maybe`.
  fwd oalg (Distr p c) = ExceptT $ oalg (Distr (fmap runExceptT p) c') where
    c' = fmap c . sequenceA

instance Functor r => Forward (Distr r) (ReaderT s) where
  fwd oalg (Distr p c) = ReaderT $ (\s -> oalg (Distr (fmap (flip runReaderT s) p) c))