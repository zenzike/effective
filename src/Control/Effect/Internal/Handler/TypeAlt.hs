{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}


module Control.Effect.Internal.Handler.TypeAlt where

import Control.Effect.Internal.Effs

import Data.Kind
import Data.Proxy
import Data.Functor.Identity
import Data.Functor.Compose
import Data.List.Kind
import Control.Monad.Trans.Compose
import Control.Monad.Trans.Identity
import Data.Iso
import Data.Coerce

-- * The primitive types of modular effect handlers


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

--newtype Runner oeffs ts fs cs = Runner {
--  getR :: forall m . cs m => Algebra oeffs m -> (forall x . ts m x -> m (Composes fs x)) }

-- * Some helper type families


-- | @Apply f a@ normalises a functor @f@ so that when it is applied to
-- @a@, any t`Identity` or t`Compose` functors are removed.
type family Apply (fs :: [k -> k]) (a :: k) where
  Apply '[] a     = a
  Apply (f:fs) a  = f (Apply fs a)

{-
newtype Comps (fs :: [Type -> Type]) (x :: Type) 
  = Comps { unComps :: Apply fs x }

newtype HComps (ts :: [(Type -> Type) -> (Type -> Type)]) 
               (m :: Type -> Type) 
               (x :: Type) 
  = HComps { unHComps :: Apply ts m x }

newtype CompsTwoA fs1 fs2 x = CompsTwoA { unCompsTwoA :: Apply fs1 (Apply fs2 x) }
newtype CompsTwoB fs1 fs2 x = CompsTwoB { unCompsTwoB :: Apply (fs1 :++ fs2) x }
-}

class (Coercible (Apply fs1 (Apply fs2 x)) (Apply (fs1 :++ fs2) x)) 
  => Assoc fs1 fs2 x where 
  assoc :: Proxy fs1 -> Proxy fs2 -> Proxy x
        -> Iso (Apply fs1 (Apply fs2 x)) (Apply (fs1 :++ fs2) x)

instance (Coercible (Apply fs1 (Apply fs2 x)) (Apply (fs1 :++ fs2) x)) 
  => Assoc fs1 fs2 x where 
  assoc _ _ _ = Iso coerce coerce 


class ( Coercible (Apply ts1 (Apply ts2 m) x) (Apply (ts1 :++ ts2) m x) ) 
  => HAssoc (ts1 :: [(Type -> Type) -> (Type -> Type)]) 
            (ts2 :: [(Type -> Type) -> (Type -> Type)]) 
            (m :: Type -> Type)
            (x :: Type) where 
  hassoc :: Proxy ts1 -> Proxy ts2 -> Proxy m 
         -> Iso (Apply ts1 (Apply ts2 m) x) (Apply (ts1 :++ ts2) m x)

instance (Coercible (Apply ts1 (Apply ts2 m) x) (Apply (ts1 :++ ts2) m x)) 
  => HAssoc (ts1 :: [(Type -> Type) -> (Type -> Type)]) 
            (ts2 :: [(Type -> Type) -> (Type -> Type)]) 
            (m :: Type -> Type)
            (x :: Type) where 
  hassoc _ _ _ = Iso coerce coerce

class (Functor (Apply ts1 (Apply ts2 m)), Functor (Apply (ts1 :++ ts2) m)) 
  => Comp2Funcs ts1 ts2 m where 
instance (Functor (Apply ts1 (Apply ts2 m)), Functor (Apply (ts1 :++ ts2) m)) 
  => Comp2Funcs ts1 ts2 m where 

--    g :: (Apply (fs1 :++ fs2) x) -> (Apply fs1 (Apply fs2 x))
--    g = (unCompsTwoA @fs1 @fs2 @x . coerce . CompsTwoB @fs1 @fs2 @x)


{-
-- The proxy arguments help with type checking because GHC doesn't think `Apply`
-- is an injective type family and struggles to check types when it is involved.
class Assoc fs1 fs2 where
  assoc  :: Proxy fs1 -> Proxy fs2 -> Proxy x
         -> Iso (Apply fs1 (Apply fs2 x)) (Apply (fs1 :++ fs2) x)

instance Assoc '[] fs2 where
  {-# INLINE assoc #-}
  assoc _ _ _ = Iso id id

class HAssoc ts1 ts2 where
  hassoc  :: Proxy ts1 -> Proxy ts2 -> Proxy m -> Proxy x
          -> Apply ts1 (Apply ts2 m) x -> Apply (ts1 :++ ts2) m x
  hassoc' :: Proxy ts1 -> Proxy ts2 -> Proxy m -> Proxy x
          -> Apply (ts1 :++ ts2) m x -> Apply ts1 (Apply ts2 m) x

class PreserveIso f where
  isoMap :: Iso a b -> Iso (f a) (f b)

instance Functor f => PreserveIso f where
  {-# INLINE isoMap #-}
  isoMap (Iso f b) = Iso (fmap f) (fmap b)

class HPreserveIso t where
  hisoMap :: (forall x. Iso (m x) (n x)) -> Iso (t m x) (t n x)


instance (Functor f, Assoc fs1 fs2) => Assoc (f:fs1) fs2 where
  {-# INLINE assoc #-}
  assoc _ pfs2 px = isoMap (assoc (Proxy :: Proxy fs1) pfs2 px)
-}