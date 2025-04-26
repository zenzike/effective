{-|
Module      : Control.Effect.Internal.AlgTrans.Type
Description : 
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}


module Control.Effect.Internal.AlgTrans.Type 
  ( AlgTrans(..)
  , AlgTransM
  , Assoc
  , Apply
  ) where

import Data.Kind
import Data.List.Kind
import Control.Effect.Internal.Effs

-- | Transforming effects @oeffs@ into effects @effs@ on a functor satisfying @cs@.
type AlgTrans
  :: [Effect]                             -- ^ effs  : input effects
  -> [Effect]                             -- ^ oeffs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ^ ts    : carrier transformer
  -> ((Type -> Type) -> Constraint)       -- ^ cs    : carrier constraint
  -> Type
newtype AlgTrans effs oeffs ts cs = AlgTrans {
   getAT :: forall m . cs m => Algebra oeffs m -> Algebra effs (Apply ts m) }

-- | Algebra transformers for monads.
type AlgTransM effs oeffs ts = AlgTrans effs oeffs ts Monad 