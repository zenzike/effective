{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.Family.Latent where

import Control.Family
import Control.Effect
import Data.HFunctor

type Latent' sig = Latent (LaZeta sig) (LaL sig)
data Latent (z :: Type -> (Type -> Type) -> Type) 
            (l :: Type -> Type) 
            (f :: Type -> Type) 
            a where
  Latent :: z p c -> l () -> (forall x. c x -> l () -> f (l x)) -> (l p -> a) -> Latent z l f a

instance Functor (Latent z l f) where
  fmap f (Latent sub l st c) = Latent sub l st (f . c)

instance HFunctor (Latent z l) where
  hmap f (Latent sub l st c) = Latent sub l (\c l -> f (st c l)) c

type family LaZeta (sig :: Effect) :: Type -> (Type -> Type) -> Type
type family LaL (sig :: Effect) :: Type -> Type

type LaFam :: Effect -> Constraint

class (HFunctor sig) => LaFam sig where
  laproject :: sig f a -> Latent (LaZeta sig) (LaL sig) f a
--   laproject' :: sig f a -> Latent sig f a

  lainject :: Latent (LaZeta sig) (LaL sig) f a -> sig f a
--   laproject' :: sig f a -> Latent (LaZeta sig) (LaL sig) f a

type instance LaZeta (Latent z l) = z
type instance LaL (Latent z l) = l

instance LaFam (Latent z l) where
  laproject = id
  lainject = id
