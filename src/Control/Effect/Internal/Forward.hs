{-|
Module      : Control.Effect.Internal.Forward
Description : Forwarding algebras
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GADTs #-}

module Control.Effect.Internal.Forward where
import Control.Effect.Internal.Effs

import Data.Kind ( Type )
import Data.HFunctor
import Data.List.Kind
import GHC.TypeNats
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Compose
import Control.Monad.Trans.Class

-- | The class demonstrating that an effect @eff@ can be forwarded through a transformer @t@.
class Forward (eff :: Effect) (t :: Effect) where
  -- | @fwd alg@ is a higher-order @eff@ algebra with carrier @m@ that will
  -- create an @eff@ algebra with carrier @t m@.
  fwd :: forall m . (Monad m)
       => (forall x . eff m x  -> m x)
       -> (forall x . eff (t m) x -> t m x)

-- | This class builds a forwarder for an t`Effs` by recursion over @effs@,
-- by ensuring that each effect can be forwarded through a given @t@.
class ForwardEffs effs (t :: (Type -> Type) -> (Type -> Type))  where
  fwdEffs :: forall m . Monad m
    => Algebra effs m
    -> Algebra effs (t m)

instance ForwardEffs '[] t where
  {-# INLINE fwdEffs #-}
  fwdEffs :: forall m . Monad m
    => Algebra '[] (m)
    -> Algebra '[] (t m)
  fwdEffs alg = absurdEffs

instance (HFunctor eff, Forward eff t, ForwardEffs effs t, KnownNat (Length effs), KnownNat (1 + Length effs)) => ForwardEffs (eff ': effs) t where
  {-# INLINE fwdEffs #-}
  fwdEffs :: forall m . Monad m => Algebra (eff ': effs) m -> Algebra (eff ': effs) (t m)
  fwdEffs alg (Eff op)   = fwd (alg . Eff) op
  fwdEffs alg (Effs ops) = fwdEffs (alg . Effs) ops

-- The `Forwards` class forwards effects through a transformer stack, assuming
-- that for each member of the stack, all operations in `effs` can be forwarded.
-- class (forall m . Monad m => Monad (HComps ts m)) => Forwards effs ts where
--   fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps ts m)
--
-- instance Forwards effs '[] where
--   fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps '[] m)
--   fwds alg = HNil . alg . hmap unHNil
--
-- instance (forall m . Monad m => Monad (t (HComps ts m)), ForwardEffs effs t, Forwards effs ts)
--   => Forwards effs (t ': ts) where
--   fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (HComps (t ': ts) m)
--   fwds alg x = HCons . fwdEffs (fwds alg) . hmap unHCons $ x

-- | This provides the `fwds` function, which forwards an algebra with carrier
-- @m@ into an algebra with carrier @t m@.
class Forwards effs t where
  fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (t m)

instance ForwardEffs effs t => Forwards effs t where
  {-# INLINE fwds #-}
  fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (t m)
  fwds alg = fwdEffs alg

instance {-# OVERLAPS #-} HFunctor (Effs effs) => Forwards effs IdentityT where
  {-# INLINE fwds #-}
  fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (IdentityT m)
  fwds alg = IdentityT . alg . hmap runIdentityT


#if MIN_VERSION_base(4,18,0)
instance {-# OVERLAPS #-} 
  ( MonadTrans t1, MonadTrans t2
  , ForwardEffs effs t1, Forwards effs t2
  , HFunctor (Effs effs)
  )
#else
instance {-# OVERLAPS #-} (MonadTrans t1, MonadTrans t2, ForwardEffs effs t1, Forwards effs t2
  , forall m . Monad m => Monad (t2 m)
  , forall m . Monad m => Monad (t1 (t2 m))
  , HFunctor (Effs effs)
  )
#endif
  => Forwards effs (ComposeT t1 t2) where
  {-# INLINE fwds #-}
  fwds :: forall m . Monad m => Algebra effs m -> Algebra effs (ComposeT t1 t2 m)
  fwds alg x = ComposeT . fwdEffs (fwds alg) . hmap getComposeT $ x
