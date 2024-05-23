{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Control.Family
  ( module Control.Family
  , Effect
  , Type
  , Constraint
  ) where

import Data.Kind ( Type, Constraint )
import Control.Effect
import GHC.Exts

type Family = Effect -> Constraint

class Family' eff where
  type FamilyType eff :: Symbol

-- instance (Family' eff, FamilyType eff ~ "alg") => Functor eff -- ... somehting to do with symbol

-- type family FAMT
--   (sig :: (Type -> Type))
--   :: (Type -> Type)   -- ??
--   -> Type             -- ??
--   -> FAMK sig
-- 
-- type family FAMK
--   (sig :: (Type -> Type))
--  :: Type
-- 
-- class FAM (sig :: (Type -> Type)) where
--   type Lower sig :: FAMK sig -> Type
-- 
--   finject :: Lower sig (FAMT sig) -> sig a
--   fproject :: sig a -> Lower sig (FAMT sig)

class Fam (sig :: Signature) where
--   type FLower sig :: (Type -> Type) -> (Type -> Type)

--   faminject :: FLower sig f a -> Flower sig a





-- aproject :: sig f a -> Algebraic (AlgSig sig) f a
-- aproject p = Algebraic 

-- ainject :: Algebraic (AlgSig sig) f a -> sig f a

-- class FAMAlg sig where

-- instance FAMAlg sig => FAM sig where
    -- finject = ... famalginject
-- instance FAMLat sig => FAM sig where


-- instance FAM Stop where
-- type Lower Stop = 
-- finject = ...
-- fproject = ...