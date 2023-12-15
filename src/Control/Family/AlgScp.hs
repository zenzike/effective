{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Control.Family.AlgScp where

import Control.Family.Scoped
import Control.Family.Algebraic
import Data.EitherF

import Control.Family.Base

type EitherAlgScp :: Effect -> Constraint
class EitherAlgScp sig where
  type EAlgScp sig :: Type -> Type
  eproject :: sig f a -> Either (Algebraic (EAlgScp sig) f a) (Scoped (EAlgScp sig) f a)

-- instance {-# INCOHERENT #-} (JustAlg sig) => EitherAlgScp sig where
--   type EAlgScp sig = JAlg sig
--   eproject = Left . Algebraic

-- instance {-# OVERLAPS #-} (JustScp sig) => EitherAlgScp sig where
--   type EAlgScp sig = JScp sig
--   eproject = Right
