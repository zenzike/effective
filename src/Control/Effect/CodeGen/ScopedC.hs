{-# LANGUAGE ImpredicativeTypes, TypeFamilies #-}
module Control.Effect.CodeGen.ScopedC where

import Control.Effect
import Control.Effect.CodeGen.Operations
import Control.Effect.CodeGen.SoPU
import Control.Effect.CodeGen.Down
import Control.Effect.CodeGen.Split
import Control.Effect.CodeGen.Gen
import Control.Effect.Family.Scoped (Scp(..))
import Data.Iso
import qualified Data.Iso as Iso
import Data.Kind (Type, Constraint)
import Data.HFunctor
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Lazy as L

-- | The family of _staged scoped_ operations, which are scoped operations with the
-- restriction that the return value must be a sum of products of code. See `scpCIso`.
data ScpC (sig :: Type -> Type) (m :: Type -> Type) (x :: Type) where
  ScpC :: sig (m (CodeQ y)) -> ((CodeQ y) -> x) -> ScpC sig m x

instance Functor (ScpC sig m) where
  fmap f (ScpC op k) = ScpC op (f . k)

instance Functor sig => HFunctor (ScpC sig) where
  hmap tau (ScpC op k) = ScpC (fmap tau op) k

-- | The isomorphism characterising t`ScpC`.
scpCIso
  :: Functor m
  => Iso (forall x. ScpC sig m x -> m x)
     (forall x. Scp sig m (CodeQ x) -> m (CodeQ x))
scpCIso = Iso fwd bwd where
  fwd :: (forall x. ScpC sig m x -> m x) -> (forall x. Scp sig m (CodeQ x) -> m (CodeQ x))
  fwd f (Scp op) = f (ScpC op id)

  bwd :: Functor m => (forall x. Scp sig m (CodeQ x) -> m (CodeQ x)) -> (forall x. ScpC sig m x -> m x)
  bwd g (ScpC op k) = fmap k $ g (Scp op)

-- | Obtaining a staged scoped operation from the code of a scoped operation.
scpC
  :: forall sig sig' m x.
     ( sig' $~> sig, Functor sig, Functor sig', Monad m )
  => CodeQ (Scp sig m -.> m)
  -> sig' (GenM m (CodeQ x))
  -> GenM m (CodeQ x)
scpC algC = scpC' (\opc -> [|| at $$algC (Scp $$opc) ||])

-- | A more flexible form of `scpC` that allows binding-time improvement.
scpC'
  :: forall sig sig' m x.
     ( sig' $~> sig, Functor sig, Functor sig', Monad m )
  => (forall x. CodeQ (sig (m x)) -> CodeQ (m x))
  -> sig' (GenM m (CodeQ x))
  -> GenM m (CodeQ x)
scpC' algC op =
 let op' = down @sig' @sig $ fmap runGenM op
 in GenM $ \k -> [|| do x <- $$(algC op'); $$(k [||x||]) ||]


instance Functor sig => Forward (ScpC sig) (ReaderT s) where
  type FwdConstraint (ScpC sig) (ReaderT s) = Functor
  fwd alg = Iso.bwd scpCIso (\(Scp op) -> ReaderT $ \r ->
    let x = fmap (flip runReaderT r) op
    in Iso.fwd scpCIso alg (Scp x))

-- | We can only forward staged scoped operations along t`MaybeT` when we also have
-- the code-generation effects to generate a case split. Consequently, this
-- forwarder doesn't fit into the `Forward` class, but we can use it manually
-- when needed.
scpCMaybeFwd :: Functor sig => AlgTrans '[ScpC sig] '[ScpC sig, CodeGen] '[MaybeT] Monad
scpCMaybeFwd = algTrans1 $ \oalg -> Iso.bwd scpCIso (\(Scp op) -> MaybeT $
  let x = fmap (fmap (down @Maybe @Maybe) . runMaybeT) op
      y = Iso.fwd scpCIso (callM oalg) (Scp x)
  in do cMb <- y; splitM oalg cMb)

scpCExceptFwd :: Functor sig => AlgTrans '[ScpC sig] '[ScpC sig, CodeGen] '[ExceptT (CodeQ e)] Monad
scpCExceptFwd = algTrans1 $ \oalg -> Iso.bwd scpCIso (\(Scp op) -> ExceptT $
  let x = fmap (fmap (down @(Either _) @(Either _)) . runExceptT) op
      y = Iso.fwd scpCIso (callM oalg) (Scp x)
  in do cMb <- y; splitM oalg cMb)

-- | We can only forward staged scoped operations along t`StateT` when we also have
-- the code-generation effects to generate a case split. Consequently, this
-- forwarder doesn't fit into the `Forward` class, but we can use it manually
-- when needed.
scpCStateFwd :: Functor sig => AlgTrans '[ScpC sig] '[ScpC sig, CodeGen] '[L.StateT (CodeQ s)] Monad
scpCStateFwd = algTrans1 $ \oalg -> Iso.bwd scpCIso (\(Scp op) -> L.StateT $ \s ->
  let x = fmap (flip L.runStateT s) op
      y = fmap (fmap (\(c1, c2) -> [|| ($$c1, $$c2) ||])) x
      z = Iso.fwd scpCIso (callM oalg) (Scp y)
  in do cp <- z; splitM oalg cp)
