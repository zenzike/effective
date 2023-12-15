{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Control.Family.Scoped where

import Control.Family.Base
import Data.EitherF
import Control.Effects

newtype Scoped lsig f x = Scoped (lsig (f x))

type JustScp :: Effect -> Constraint
class JustScp sig where
  type JScp sig :: Type -> Type
  sproject :: sig f a -> Scoped (JScp sig) f a

instance JustScp (Scoped lsig) where
  type JScp (Scoped lsig) = lsig
  sproject = id

instance JustScp (Effs '[]) where
  type JScp (Effs '[]) = VoidF
  sproject = absurdEffs

instance (JustScp sig, JustScp (Effs sigs)) => JustScp (Effs (sig ': sigs)) where
  type JScp (Effs (sig ': sigs)) = EitherF (JScp sig) (JScp (Effs sigs))
  sproject (Eff x) = let (Scoped x') = sproject x in Scoped (InlF x')
  sproject (Effs y) = let (Scoped y') = sproject y in Scoped (InrF y')
