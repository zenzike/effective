{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Control.Family.Algebraic where

import Control.Family.Base
import Data.EitherF
import Control.Effects
import Data.HFunctor

newtype Algebraic (lsig :: Type -> Type)
                  (f :: Type -> Type) 
                  x
                  = Algebraic (lsig x)

instance Functor lsig => Functor (Algebraic lsig f) where
  fmap f (Algebraic x) = Algebraic (fmap f x)

instance Functor lsig => HFunctor (Algebraic lsig) where
  hmap f (Algebraic x) = Algebraic x

-- `AlgSig sig` is the (lower-order) signature of algebraic operations
-- associated to an higher-order effect `sig`.
-- It ought to be a member of the class `AlgSig` but we also want to use it for
-- the class `ASFam` so it is defined globally here.
type family AlgSig (sig :: Effect) :: (Type -> Type)

-- An effect is in the family of algebraic operations if it 
-- is isomorphic to `Algebraic lsig` for some functor `lsig`
type AlgFam :: Effect -> Constraint
class (HFunctor sig, Functor (AlgSig sig)) => AlgFam sig where
  aproject :: sig f a -> Algebraic (AlgSig sig) f a
  ainject :: Algebraic (AlgSig sig) f a -> sig f a
  ainject (Algebraic x) = ainject' x

  ainject' :: AlgSig sig a -> sig f a
  ainject' = ainject . Algebraic


type instance AlgSig (Algebraic lsig) = lsig
instance Functor lsig => AlgFam (Algebraic lsig) where
  aproject = id
  ainject = id

-- TODO: Converting between `Effs sigs` and `Algebraic lsig` is very common in
-- the library. How can we change the interface of AlgFam so that the following
-- two instances become id?
type instance AlgSig (Effs '[]) = VoidF
instance AlgFam (Effs '[]) where
  aproject = absurdEffs
  ainject (Algebraic x) = absurdVoidF x

type instance AlgSig (Effs (sig ': sigs)) = EitherF (AlgSig sig) (AlgSig (Effs sigs))
instance (AlgFam sig, AlgFam (Effs sigs)) => AlgFam (Effs (sig ': sigs)) where
  aproject (Eff x) = let (Algebraic x') = aproject x in Algebraic (InlF x')
  aproject (Effs y) = let (Algebraic y') = aproject y in Algebraic (InrF y')
  ainject (Algebraic (InlF a)) = Eff (ainject (Algebraic a)) 
  ainject (Algebraic (InrF b)) = Effs (ainject (Algebraic b))

absurdVoidAlg :: Algebraic VoidF f a -> b
absurdVoidAlg (Algebraic x) = absurdVoidF x

class ShowAlgOp (lsig :: Type -> Type) where
  showAlgOperator :: lsig x -> String
  showAlgOperands :: Show x => lsig x -> String 

instance (ShowAlgOp lsig, Show a) => Show (Algebraic lsig f a) where
  show (Algebraic x) = showAlgOperator x ++ " (" ++ showAlgOperands x ++ ") "
