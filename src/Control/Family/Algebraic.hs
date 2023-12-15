{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Control.Family.Algebraic where

import Control.Family.Base
import Data.EitherF
import Control.Effects

newtype Algebraic lsig f x = Algebraic (lsig x)

type JustAlg :: Effect -> Constraint
class JustAlg sig where
  type JAlg sig :: Type -> Type
  aproject :: sig f a -> Algebraic (JAlg sig) f a

instance JustAlg (Algebraic lsig) where
  type JAlg (Algebraic lsig) = lsig
  aproject = id

instance JustAlg (Effs '[]) where
  type JAlg (Effs '[]) = VoidF
  aproject = absurdEffs

instance (JustAlg sig, JustAlg (Effs sigs)) => JustAlg (Effs (sig ': sigs)) where
  type JAlg (Effs (sig ': sigs)) = EitherF (JAlg sig) (JAlg (Effs sigs))
  aproject (Eff x) = let (Algebraic x') = aproject x in Algebraic (InlF x')
  aproject (Effs y) = let (Algebraic y') = aproject y in Algebraic (InrF y')
