{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Control.Family.Algebraic where

import Control.Family.Base
import Data.EitherF
import Control.Effects
import Data.HFunctor

newtype Algebraic lsig f x = Algebraic (lsig x)

instance Functor lsig => Functor (Algebraic lsig f) where
  fmap f (Algebraic x) = Algebraic (fmap f x)

instance Functor lsig => HFunctor (Algebraic lsig) where
  hmap f (Algebraic x) = Algebraic x

type JustAlg :: Effect -> Constraint
class (HFunctor sig, Functor (JAlg sig)) => JustAlg sig where
  type JAlg sig :: Type -> Type
  aproject :: sig f a -> Algebraic (JAlg sig) f a
  ainject :: Algebraic (JAlg sig) f a -> sig f a
  ainject (Algebraic x) = ainject' x

  ainject' :: JAlg sig a -> sig f a
  ainject' = ainject . Algebraic

instance Functor lsig => JustAlg (Algebraic lsig) where
  type JAlg (Algebraic lsig) = lsig
  aproject = id
  ainject = id

instance JustAlg (Effs '[]) where
  type JAlg (Effs '[]) = VoidF
  aproject = absurdEffs
  ainject (Algebraic x) = absurdVoidF x

instance (JustAlg sig, JustAlg (Effs sigs)) => JustAlg (Effs (sig ': sigs)) where
  type JAlg (Effs (sig ': sigs)) = EitherF (JAlg sig) (JAlg (Effs sigs))
  aproject (Eff x) = let (Algebraic x') = aproject x in Algebraic (InlF x')
  aproject (Effs y) = let (Algebraic y') = aproject y in Algebraic (InrF y')
  ainject (Algebraic (InlF a)) = Eff (ainject (Algebraic a)) 
  ainject (Algebraic (InrF b)) = Effs (ainject (Algebraic b))
