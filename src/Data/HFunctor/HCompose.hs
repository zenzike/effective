module Data.HFunctor.HCompose where

import Data.HFunctor
import Control.Monad.Trans.Class
import Data.Kind (Type)
import Control.Monad       (liftM, ap)


-- HCompose is for composing monad transformers. Use HCompose' below
-- for composing HFunctor. Although it is the same underlying definition,
-- Haskell's typeclass resolution algorithm forces us to write two.

newtype HCompose (h :: (Type -> Type) -> (Type -> Type))
                 (k :: (Type -> Type) -> (Type -> Type))
                 (f :: (Type -> Type)) (a :: Type)
  = HCompose { getHCompose :: h (k f) a }

-- Monad transformers are closed under HCompose
instance (MonadTrans t1, MonadTrans t2) => MonadTrans (HCompose t1 t2) where
  lift x = HCompose (lift (lift x))

instance (MonadTrans t1, MonadTrans t2, Monad m) => Monad (HCompose t1 t2 m) where
  HCompose mx >>= f = HCompose (mx >>= getHCompose . f)

instance (MonadTrans t1, MonadTrans t2, Monad m) => Applicative (HCompose t1 t2 m) where
    pure x = HCompose (return x)
    (<*>) = ap

instance (MonadTrans t1, MonadTrans t2, Monad m) => Functor (HCompose t1 t2 m) where
    fmap = liftM


-- HFunctors are closed under HCompose, but we can't write
--
--    instance (HFunctor h, HFunctor k) => HFunctor (HCompose h k) where
--      hmap h (HCompose x) = HCompose (hmap (hmap h) x)
--    
--    instance (HFunctor h, HFunctor k, Functor f) => Functor (HCompose h k f) where
--      ...
--
--  because the second instance would overlap with 
--    instance (MonadTrans t1, MonadTrans t2, Monad m) => Functor (HCompose t1 t2 m) where
--
--  Therefore we need a new wrapper for composing HFunctors.

newtype HCompose' (h :: (Type -> Type) -> (Type -> Type))
                  (k :: (Type -> Type) -> (Type -> Type))
                  (f :: (Type -> Type)) (a :: Type)
  = HCompose' { getHCompose' :: h (k f) a }

instance (HFunctor h, HFunctor k) => HFunctor (HCompose' h k) where
  hmap h (HCompose' x) = HCompose' (hmap (hmap h) x)

instance (HFunctor h, HFunctor k, Functor f) => Functor (HCompose' h k f) where
  fmap i (HCompose' x) = HCompose' (fmap i x)

castHCompose :: HCompose h k f a -> HCompose' h k f a
castHCompose = HCompose' . getHCompose

castHCompose' :: HCompose' h k f a -> HCompose h k f a
castHCompose' = HCompose . getHCompose'
