{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Control.Family.Scoped where

import Control.Family
import Data.EitherF
import Control.Effect
import Data.HFunctor

newtype Scoped (lsig :: Type -> Type)
               (f :: Type -> Type) 
               x
               = Scoped (lsig (f x))

instance (Functor lsig, Functor f) => Functor (Scoped lsig f) where
  fmap f (Scoped x) = Scoped (fmap (fmap f) x)

instance Functor lsig => HFunctor (Scoped lsig) where
  hmap f (Scoped x) = Scoped (fmap f x)

type family ScpSig (sig :: Effect) :: (Type -> Type)

type ScpFam :: Effect -> Constraint
class (HFunctor sig, Functor (ScpSig sig)) => ScpFam sig where
  sproject :: sig f a -> Scoped (ScpSig sig) f a

  sinject :: Scoped (ScpSig sig) f a -> sig f a
  sinject (Scoped x) = sinject' x

  sinject' :: ScpSig sig (f a) -> sig f a
  sinject' = sinject . Scoped

type instance ScpSig (Scoped lsig) = lsig
instance (Functor lsig) => ScpFam (Scoped lsig) where
  sproject = id
  sinject = id

type instance ScpSig (Effs '[]) = VoidF
instance ScpFam (Effs '[]) where
  sproject = absurdEffs
  sinject (Scoped x) = absurdVoidF x 

type instance ScpSig (Effs (sig ': sigs)) = EitherF (ScpSig sig) (ScpSig (Effs sigs))
instance (ScpFam sig, ScpFam (Effs sigs)) => ScpFam (Effs (sig ': sigs)) where
  sproject (Eff x) = let (Scoped x') = sproject x in Scoped (InlF x')
  sproject (Effs y) = let (Scoped y') = sproject y in Scoped (InrF y')

  sinject (Scoped (InlF a)) = Eff (sinject (Scoped a)) 
  sinject (Scoped (InrF b)) = Effs (sinject (Scoped b))


absurdVoidScp :: Scoped VoidF f a -> b
absurdVoidScp (Scoped x) = absurdVoidF x

-- class ShowScpOp (lsig :: Type -> Type) where
--   showScpOperator :: lsig (f x) -> String
--   showScpOperands :: (Show (f x)) => lsig (f x) -> String 
-- 
-- instance (ShowScpOp lsig, Show (f a)) => Show (Scoped lsig f a) where
--   show (Scoped x) = showScpOperator x ++ " {" ++ showScpOperands x ++ "} "

deriving instance
  ( ShowFunctor lsig
  , ShowFunctor f
  , Show a)
  => Show (Scoped lsig f a)