{-# LANGUAGE ImpredicativeTypes, QuantifiedConstraints, UndecidableInstances, UndecidableSuperClasses, MonoLocalBinds #-}
module Control.Effect.Internal.Handler.LowLevel where

import Control.Effect.Internal.Handler.Type
import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Forward

import GHC.Base
import Unsafe.Coerce


import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity (IdentityT (..))
import Control.Monad.Trans.Compose

import Data.List.Kind

import Data.Functor.Identity
import Data.Functor.Compose
import Data.HFunctor

-- | Transforming effects @oeffs@ into effects @effs@ on a functor satisfying @cs@.
type AlgTrans
  :: [Effect]                             -- ^ effs  : input effects
  -> [Effect]                             -- ^ oeffs : output effects
  -> ((Type -> Type) -> (Type -> Type))   -- ^ ts    : carrier transformer
  -> ((Type -> Type) -> Constraint)       -- ^ cs    : carrier constraint
  -> Type
type AlgTrans effs oeffs ts cs = 
   forall m . cs m => Algebra oeffs m -> Algebra effs (ts m)

-- | Running a carrier transformer @ts@, resulting in a functor @fs@.
type Runner
  :: [Effect]                             -- ^ oeffs : output effects
  -> ((Type -> Type) -> (Type -> Type))   -- ^ ts    : carrier transformer
  -> (Type -> Type)                       -- ^ fs    : result functor
  -> ((Type -> Type) -> Constraint)       -- ^ cs    : carrier constraint
  -> Type

type Runner oeffs ts fs cs = 
  forall m . cs m => Algebra oeffs m -> (forall x . ts m x -> m (fs x))

-- * Using algebra transformers and runners 
--
-- The type families @`HApply` ts@ and @`Apply` fs@ remove newtype wrappers so
-- it is safe to coerce them into @ts@ and @fs@ respectively. (I don't know how
-- to convince GHC that this is a safe coerce.) 

under :: a -> (a -> b) -> b
under x f = f x

under' :: (a -> b) -> (b -> c) -> a -> c
under' f g = g . f

{-# INLINE evalTr #-}
evalTr :: forall effs ts cs m a. 
       ( HFunctor (Effs effs) 
       , cs m
       , Monad (ts m) 
       )
       => AlgTrans effs '[] ts cs
       -> Prog effs a
       -> HApply ts m a
evalTr alg = eval (alg absurdEffs) 
  `under'` unsafeCoerce @(ts m a) @(HApply ts m a) 

{-# INLINE run #-}
run :: forall oeffs ts fs cs m x.
       cs m 
    => Runner oeffs ts fs cs 
    -> Algebra oeffs m 
    -> ts m x -> m (Apply fs x)
run r oalg t = (r oalg t) 
  `under` unsafeCoerce @(m (fs x)) @(m (Apply fs x)) 

-- * Building algebra transformers

class (m ~ n) => Is m n where
instance (m ~ n) => Is m n where

-- | Treating an algebra on @m@ as a trivial algebra transformer that only works
-- when the carrier is exactly @m@.
{-# INLINE asTrans #-}
asTrans :: forall effs m. 
           Algebra effs m 
        -> AlgTrans effs '[] IdentityT (Is m)
asTrans alg _  = alg
  `under` unsafeCoerce @(Algebra effs m) @(Algebra effs (IdentityT m)) 

-- | The identity algebra transformer.
{-# INLINE idTrans #-}
idTrans :: forall effs cs. AlgTrans effs effs IdentityT cs
idTrans (alg :: Algebra effs m) = alg
  `under` unsafeCoerce @(Algebra effs m) @(Algebra effs (IdentityT m)) 

class (cs2 m, cs1 (ts2 m)) => CompTransC ts2 cs1 cs2 m where
instance (cs2 m, cs1 (ts2 m)) => CompTransC ts2 cs1 cs2 m where

{-# INLINE compTrans #-}
compTrans :: forall effs1 effs2 effs3 ts1 ts2 cs1 cs2.
             AlgTrans effs1 effs2 ts1 cs1
          -> AlgTrans effs2 effs3 ts2 cs2
          -> AlgTrans effs1 effs3 (ts1 `ComposeT` ts2) (CompTransC ts2 cs1 cs2)
compTrans alg1 alg2 oalg = alg1 (alg2 oalg)
  `under` unsafeCoerce @(Algebra effs1 (ts1 (ts2 _))) 
                       @(Algebra effs1 (ComposeT ts1 ts2 _))

-- * Building runners

{-# INLINE idRunner #-}
idRunner :: (forall m. cs m => Functor m) 
         => Runner effs IdentityT Identity cs
idRunner _ (IdentityT x) = fmap Identity x