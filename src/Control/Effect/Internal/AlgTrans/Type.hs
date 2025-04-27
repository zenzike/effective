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
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}


module Control.Effect.Internal.AlgTrans.Type where

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

-- * Constraints 

-- | The always true constraint.
class    TruthC (m :: Type -> Type) where
instance TruthC m where

-- | A constraint synonym that is frequently used when composing algebra transformers. 
class    (cs2 m, cs1 (Apply ts2 m)) => CompC ts2 cs1 cs2 m where
instance (cs2 m, cs1 (Apply ts2 m)) => CompC ts2 cs1 cs2 m where

-- | A synonym for the conjunction of two constraints @cs1@ and @cs2@ on @m@.
class    (cs1 m, cs2 m) => AndC cs1 cs2 m where
instance (cs1 m, cs2 m) => AndC cs1 cs2 m where

-- | A synonym for the implication of two constraints.
class    (forall m. c m => d m) => ImpliesC c d where
instance (forall m. c m => d m) => ImpliesC c d where

-- | Because `Apply` is not injective, we can't do quantified constraint @forall m. Monad (Apply ts m)@
-- but we can do @forall m. MonadApply ts m@.
class    (Monad (Apply ts m)) => MonadApply ts m where
instance (Monad (Apply ts m)) => MonadApply ts m where