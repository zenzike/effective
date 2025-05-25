{-|
Module      : Control.Effect.Scoped
Description : The scoped effect family
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

A scoped operation of signature @sig :: Type -> Type@ on a monad @m@ is a
function @s :: forall x. sig (m x) -> m x@. Unlike \'algebraic operations\'
defined in "Control.Effect.Family.Algebraic", scoped operations don't need
to satisfy the equation:

> s x >>= k  ==  s (fmap (>>= k) x)

so the operation @s@ intuitively delimits a boundary between its argument
@x@ and the rest of the computation @k@. The effect of @s@ is applied only
to its \'scope\' @x@. Important examples are scoped operations include

1. exception catching @catch p q@,
2. semi-deterministic operator @once@ in logic programming,
3. parallel composition @p || q@ in concurrency.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Family.Scoped where

import Control.Effect

import Data.Kind ( Type )
import Data.HFunctor
import qualified Data.Functor.Unary as U

import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State.Strict
import qualified Control.Monad.Trans.State.Lazy as L
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader
import Control.Monad.Trans.List
import Control.Monad.Trans.Resump
import Control.Monad.Trans.Identity

-- | The family of scoped operations. Forwarding scoped operations through a
-- transformer must be given explicitly using the `Forward` class.
newtype Scp (sig :: Type -> Type)
         (f :: Type -> Type)
         k
         = Scp (sig (f k))
{-
We can optimise the constructor @Scp@ by using a Coyoneda representation so that
instead the constructor becomes:

> forall x y . Scp !(sig x) !(x -> f y) !(y -> k)

But this creates 2 additional fields, and `hmap` is not often used.
Benchmarks reveal that applying coyoneda only to the data yields
marginally less allocation and time.
-}

instance (Functor sig, Functor f) => Functor (Scp sig f) where
  {-# INLINE fmap #-}
  fmap f (Scp op) = Scp (fmap (fmap f) op)

instance Functor sig => HFunctor (Scp sig) where
  {-# INLINE hmap #-}
  hmap h (Scp op) = Scp (fmap h op)

instance Functor sig => Forward (Scp sig) IdentityT where
  type FwdConstraint (Scp sig) IdentityT = Functor
  {-# INLINE fwd #-}
  fwd alg (Scp op) = IdentityT (alg (Scp (fmap runIdentityT op)))

instance Functor sig => Forward (Scp sig) (ExceptT e) where
  type FwdConstraint (Scp sig) (ExceptT e) = Functor
  {-# INLINE fwd #-}
  fwd alg (Scp op) = ExceptT (alg (Scp (fmap runExceptT op)))

instance Functor sig => Forward (Scp sig) MaybeT where
  type FwdConstraint (Scp sig) MaybeT = Functor
  {-# INLINE fwd #-}
  fwd alg (Scp op) = MaybeT (alg (Scp (fmap runMaybeT op)))

instance Functor sig => Forward (Scp sig) (StateT s) where
  type FwdConstraint (Scp sig) (StateT s) = Functor
  {-# INLINE fwd #-}
  fwd alg (Scp op) = StateT (\s -> (alg (Scp (fmap (flip runStateT s) op))))

instance Functor sig => Forward (Scp sig) (L.StateT s) where
  type FwdConstraint (Scp sig) (L.StateT s) = Functor
  {-# INLINE fwd #-}
  fwd alg (Scp op) = L.StateT (\s -> (alg (Scp (fmap (flip L.runStateT s) op))))

instance Functor sig => Forward (Scp sig) (WriterT s) where
  type FwdConstraint (Scp sig) (WriterT s) = Functor
  {-# INLINE fwd #-}
  fwd alg (Scp op) = WriterT (alg (Scp (fmap runWriterT op)))

instance Functor sig => Forward (Scp sig) (ReaderT w) where
  type FwdConstraint (Scp sig) (ReaderT w) = Functor
  {-# INLINE fwd #-}
  fwd alg (Scp op) = ReaderT (\r -> alg (Scp (fmap (flip runReaderT r) op)))

-- | Unary scoped operations can be forwarded by `ListT` by applying the
-- operation recursively to all @m@-actions inside the `ListT` value.
instance U.Unary sig => Forward (Scp sig) ListT where
  type FwdConstraint (Scp sig) ListT = Functor
  fwd :: forall m. Functor m => (forall x. Scp sig m x -> m x) 
      -> (forall x. Scp sig (ListT m) x -> ListT m x)
  fwd alg (Scp op) = hmap ualg (U.get op) where
    ualg :: forall y. m y -> m y
    ualg op' = alg (Scp (U.upd op op'))

instance (Functor s, U.Unary sig) => Forward (Scp sig) (ResT s) where
  type FwdConstraint (Scp sig) (ResT s) = Functor
  fwd :: forall m. Functor m => (forall x. Scp sig m x -> m x) 
      -> (forall x. Scp sig (ResT s m) x -> ResT s m x)
  fwd alg (Scp op) = hmap ualg (U.get op) where
    ualg :: forall y. m y -> m y
    ualg op' = alg (Scp (U.upd op op'))