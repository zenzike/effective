{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.Family.AlgScp 
  ( ASFam (..)
  , module Control.Family.Algebraic
  , module Control.Family.Scoped
  ) where

import Control.Family.Base
import Control.Family.Algebraic
import Control.Family.Scoped
import Data.EitherF
import Control.Effect
import Data.HFunctor

type ASFam :: Effect -> Constraint

-- `ASFam sig` means that `sig` is isomorphic to the coproduct of an algebraic
-- operation of signature `AlgSig sig` and scoped operation of signature `ScpSig sig`.
class (HFunctor sig, Functor (ScpSig sig), Functor (AlgSig sig)) => ASFam sig where
  asproject :: sig f a -> Either (Algebraic (AlgSig sig) f a)
                                 (Scoped (ScpSig sig) f a)
  asinject  :: Either (Algebraic (AlgSig sig) f a) 
                      (Scoped (ScpSig sig) f a) 
            -> sig f a
  asinject = either (\(Algebraic x) -> asinjectAlg x) (\(Scoped x) -> asinjectScp x)

  asinjectAlg :: AlgSig sig a -> sig f a 
  asinjectAlg = asinject . Left . Algebraic

  asinjectScp :: ScpSig sig (f a) -> sig f a 
  asinjectScp = asinject . Right . Scoped

-- `AlgSig (Algebraic lsig)` is already defined in Control.Family.Algebraic
type instance ScpSig (Algebraic lsig) = VoidF
instance Functor lsig => ASFam (Algebraic lsig) where
  asproject = Left
  asinject (Left x) = x
  asinject (Right (Scoped x)) = absurdVoidF x

-- `ScpSig (Scoped lsig)` is already defined in Control.Family.Scoped
type instance AlgSig (Scoped lsig) = VoidF
instance Functor lsig => ASFam (Scoped lsig) where
  asproject = Right
  asinject (Left (Algebraic x)) = absurdVoidF x
  asinject (Right x) = x

instance ASFam (Effs '[]) where
  asproject = absurdEffs
  asinject = either absurdVoidAlg absurdVoidScp

instance (ASFam sig, ASFam (Effs sigs)) => ASFam (Effs (sig ': sigs)) where
  asproject (Eff x) = let x' = asproject x in 
    either (\(Algebraic x'') -> Left (Algebraic (InlF x''))) 
           (\(Scoped x'')    -> Right (Scoped (InlF x''))) x'

  asproject (Effs x) = let x' = asproject x in 
    either (\(Algebraic x'') -> Left (Algebraic (InrF x''))) 
           (\(Scoped x'')    -> Right (Scoped (InrF x''))) x'

  asinject (Left (Algebraic (InlF a))) = Eff (asinject (Left (Algebraic a)))
  asinject (Right (Scoped (InlF a)))   = Eff (asinject (Right (Scoped a)))
  asinject (Left (Algebraic (InrF a))) = Effs (asinject (Left (Algebraic a)))
  asinject (Right (Scoped (InrF a)))   = Effs (asinject (Right (Scoped a)))
