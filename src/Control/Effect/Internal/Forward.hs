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
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_HADDOCK ignore-exports #-}

module Control.Effect.Internal.Forward (Forward (..), Forwards (..)) where

import Data.Kind
import Data.List.Kind
import Control.Effect.Internal.Effs
import Control.Effect.Internal.AlgTrans.Type
import qualified Control.Effect.Internal.Forward.ForwardC as F

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

instance Forward effs t => F.ForwardC effs t where
  type FwdConstraint effs t = Monad

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

class (F.Forwards Monad effs ts) => Forwards effs ts where
  fwds :: forall m. Monad m => Algebra effs m -> Algebra effs (Apply ts m)

instance (F.ForwardsC effs ts, Monad `ImpliesC` (F.FwdsConstraint effs ts)) => Forwards effs ts where
  {-# INLINE fwds #-}
  fwds = getAT (F.fwdsC @effs @ts)