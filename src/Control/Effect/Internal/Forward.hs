{-|
Module      : Control.Effect.Internal.Forward
Description : Forwarding algebras
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental

This module is a specialisation of the module "Control.Effect.Internal.Handler.Forward" 
specialised to the constraint of monads.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_HADDOCK ignore-exports #-}

module Control.Effect.Internal.Forward (Forward(..), fwds, Forwards) where

import Data.Kind
import Control.Effect.Internal.Effs
import qualified Control.Effect.Internal.Forward.ForwardC as F
import Control.Effect.Internal.Handler.Type

-- | The class demonstrating that an effect @eff@ can be forwarded through a transformer @t@.
-- This is the typeclass that the user of @effective@ should instantiate and it will be used
-- to automatically discharge constraints of `Forwards`.
-- 
-- `Forward` is a wrapper of `F.Forward` specialised to the constraint of monads. This is a 
-- typeclass that the library user will define instances for, so we create a new
-- typeclass that implies the internal typeclass `F.Forward`.
type Forward :: Effect -> ((Type -> Type) -> (Type -> Type)) -> Constraint
class Forward eff t where 
  fwd :: forall m . Monad m
      => (forall x . eff m x  -> m x)
      -> (forall x . eff (t m) x -> t m x)

instance Forward effs t => F.ForwardC Monad effs t where
  {-# INLINE fwdC #-}
  fwdC = Control.Effect.Internal.Forward.fwd


-- | This provides the `fwds` function, which forwards an algebra with carrier
-- @m@ into an algebra with carrier @t m@. This is a typeclass that the user 
-- of @effective@ should use but not instantiate, because it is automatically
-- discharged using `Forward`.
--
-- `Forwards` is a wrapper of `F.Forwards` specialised to the constraint of monads. 
-- This is a typeclass that the library user will assume, so we create a new typeclass
-- that is implied by the internal typeclass.

type Forwards :: [Effect] -> [(Type -> Type) -> (Type -> Type)] -> Constraint
class F.ForwardsC Monad effs ts => Forwards effs ts where
  {-# INLINE fwds #-}
  fwds :: forall m. Monad m => Algebra effs m -> Algebra effs (Apply ts m)
  fwds = getAT (F.fwdsC @Monad @effs @ts)

instance F.ForwardsC Monad effs ts => Forwards effs ts where