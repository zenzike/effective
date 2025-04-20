{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}


module Control.Effect.Internal.Handler.Type where

import Data.Kind
import Data.Functor.Identity
import Data.Functor.Compose
import Data.List.Kind
import Control.Monad.Trans.Compose
import Control.Monad.Trans.Identity

-- | @Apply f a@ normalises a functor @f@ so that when it is applied to
-- @a@, any t`Identity` or t`Compose` functors are removed.
type family Apply f a where
  Apply Identity a      = a
  Apply (Compose f g) a = Apply f (Apply g a)
  Apply f a             = f a

-- | @HApply@ normalises a higher-order functor @h@ so that when it is applied to
-- @f@, any t`IdentityT` or t`ComposeT` higher-order functors are removed.
type family HApply
  (h :: (Type -> Type) -> (Type -> Type))
  (f :: Type -> Type) :: (Type -> Type)
  where
  HApply IdentityT        f = f
  HApply (ComposeT h1 h2) f = h1 (h2 f)
  HApply h  f               = h f

-- TODO: Implement O(n) version
-- | @Functors f@ builds a list of all the functors composed using t`Compose` to make @f@,
-- while removing any instances of t`Identity`.
type family Functors (f :: (Type -> Type)) :: [Type -> Type] where
  Functors (Compose f g) = Functors f :++ Functors g
  Functors (Identity)    = '[]
  Functors f             = '[f]

-- | @HFunctors h@ builds a list of all the functors composed using t`ComposeT` to make @h@,
-- while removing any instances of t`IdentityT`.
type family HFunctors (h :: (Type -> Type) -> (Type -> Type))
  :: [(Type -> Type) -> (Type -> Type)] where
  HFunctors (ComposeT h k) = HFunctors h :++ HFunctors k
  HFunctors (IdentityT)    = '[]
  HFunctors h              = '[h]

-- | @RAssoc f@ reassociates any t`Compose` functors in @f@ to the right,
-- and removes any t`Identity` functors. If @f@ is the t`Identity` functor,
-- then @f@ is returned.
type family RAssoc f where
  RAssoc f = Foldr0 Compose Identity (Functors f)

-- | @HRAssoc h@ reassociates any t`ComposeT` functors in @h@ to the right,
-- and removes any t`IdentityT` functors. If @h@ is the t`IdentityT` higher-order
-- functor, then @h@ is returned.
type family HRAssoc f where
  HRAssoc f = Foldr0 ComposeT IdentityT (HFunctors f)

