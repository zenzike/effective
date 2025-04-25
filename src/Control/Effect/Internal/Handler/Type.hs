{-|
Module      : Control.Effect.Internal.Handler.Type
Description : Algebra transformers and runners
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}


module Control.Effect.Internal.Handler.Type where

import Data.Kind
import Data.List.Kind
import Control.Effect.Internal.Effs

-- * The primitive types for modular effect handlers

-- | @Apply fs a@ applies a list @fs@ of type-level functions to the given @a@.
type family Apply (fs :: [k -> k]) (a :: k) where
  Apply '[] a     = a
  Apply (f:fs) a  = f (Apply fs a)

-- | For all closed type-level lists @fs1@ and @fs2@, the type @Apply fs1 (Apply fs2 a)@ 
-- and @@Apply (fs1 :++ fs2) a@ will be exactly the same, but GHC doesn't know this, so
-- whenever we need this, we will need to manually assume this as a constraint @Assoc fs1 fs2 a@,
-- which is going to be automatically discharged when @fs1@ and @fs2@ are substituted by closed lists.

class (Apply fs1 (Apply fs2 a) ~ Apply (fs1 :++ fs2) a) => Assoc fs1 fs2 a where
instance (Apply fs1 (Apply fs2 a) ~ Apply (fs1 :++ fs2) a) => Assoc fs1 fs2 a where

-- | Transforming effects @oeffs@ into effects @effs@ on a functor satisfying @cs@.
type AlgTrans
  :: [Effect]                             -- ^ effs  : input effects
  -> [Effect]                             -- ^ oeffs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ^ ts    : carrier transformer
  -> ((Type -> Type) -> Constraint)       -- ^ cs    : carrier constraint
  -> Type
newtype AlgTrans effs oeffs ts cs = AlgTrans {
   getAT :: forall m . cs m => Algebra oeffs m -> Algebra effs (Apply ts m) }

-- | Running a carrier transformer @ts@, resulting in a functor @fs@.
type Runner
  :: [Effect]                             -- ^ oeffs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ^ ts    : carrier transformer
  -> [Type -> Type]                       -- ^ fs    : result functor
  -> ((Type -> Type) -> Constraint)       -- ^ cs    : carrier constraint
  -> Type
newtype Runner oeffs ts fs cs = Runner {
  getR :: forall m . cs m => Algebra oeffs m -> (forall x . Apply ts m x -> m (Apply fs x)) }