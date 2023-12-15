{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Control.Effect.MCarrier where


import Control.Handler
import Control.Effects
import Control.Family.Base
import Control.Family.Algebraic
import Data.Functor.Identity
import Control.Monad.Trans.Cont
import Data.Functor.Composes

-- Modular carriers
-- ----------------
--
-- So far the carriers of our library have always been a monad:
-- the algebras in a `Handler` are always of some monad `m`.
-- However, this is not always possible or desirable.
-- For example, although it is known that the (functorial)
-- composition of two applicatives is applicative, the
-- composition of two monads need not be a monad. Concretely,
-- the composition of `m` and the list monad `[]` is not a monad
-- (sometimes called `ListT` done wrong). It can be modelled
-- by `m [x]` for all x. Such a functor can nevertheless be a carrier:
data ListC m x = ListC (m [x])

-- The caveat is that we can use this carrier for nondet computations so long
-- as there are no scoped operations such as `search` or `once`.
--
-- Another example is ContT; since there only algebraic operations
-- can be forwarded.
data Carrier c f asig = Carrier
  { crun :: forall m x . Monad m => c m x -> m (f x)
  , calg :: forall m x . Monad m => asig (c m x) -> c m x
  , cfwd :: forall m x . Monad m => m (c m x) -> c m x
  , cgen :: forall m x . Monad m => x -> c m x
  }

newtype ContC (c :: (Type -> Type) -> Type -> Type) (m :: Type -> Type) x
  = ContC (forall y . Cont (c m y) x)
  deriving Functor

convert :: forall c f asig . (Functor f, Functor asig)
  => Carrier c f asig -> Handler' '[Algebraic asig] '[] (ContC c) '[f] JustAlg
convert (Carrier crun calg cfwd cgen) = Handler' run alg fwd where
  run :: Monad m
      => (forall x. Effs '[] m x -> m x)
      -> (forall x. ContC c m x -> m (Comps '[f] x))
  run _ (ContC mx) = fmap comps $ crun (runCont mx cgen)

  alg :: forall m . Monad m
      => (forall x. Effs '[] m x -> m x)
      -> (forall x. Effs '[Algebraic asig] (ContC c m) x -> ContC c m x)
  alg _ (Eff (Algebraic x)) = ContC (cont (\k -> calg (fmap k x)))


  fwd :: (JustAlg sig, Monad m)
      => (forall x. sig m x -> m x)
      -> (forall x. sig (ContC c m) x -> ContC c m x)
  fwd alg op = let (Algebraic op') = aproject op
               in ContC (cont (\k -> cfwd (alg (ainject' (fmap k op')))))
