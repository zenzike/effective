{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}

module Control.Effect.Internal.MAlgebra where

import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs.Type
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Forward
import Control.Effect.Internal.Handler

import Data.HFunctor
import Data.Functor.Identity
import Data.Functor.Compose

import Control.Monad.Trans.Class
import Control.Applicative

import GHC.TypeLits
import Unsafe.Coerce
import Data.Coerce
import Data.List.Kind
import Data.Kind (Type)



class MAlgebra t where
  type IEffs t :: [Effect]
  type OEffs t :: [Effect]
  malg :: Monad m => Algebra (OEffs t) m
                  -> Algebra (IEffs t) (t m)


newtype FuseT (h :: (Type -> Type) -> (Type -> Type))
                 (k :: (Type -> Type) -> (Type -> Type))
                 (f :: (Type -> Type)) (a :: Type)
  = FuseT { getFuseT :: h (k f) a }

instance (Applicative m, Alternative (t1 (t2 m))) => Alternative (FuseT t1 t2 m) where
  empty :: forall a . FuseT t1 t2 m a
  empty = coerce (empty :: t1 (t2 m) a)

  (<|>) :: forall a . FuseT t1 t2 m a -> FuseT t1 t2 m a -> FuseT t1 t2 m a
  (<|>) = coerce ((<|>) :: t1 (t2 m) a -> t1 (t2 m) a -> t1 (t2 m) a)

  many :: forall a . FuseT t1 t2 m a -> FuseT t1 t2 m [a]
  many = coerce (many :: t1 (t2 m) a -> t1 (t2 m) [a])

  some :: forall a . FuseT t1 t2 m a -> FuseT t1 t2 m [a]
  some = coerce (some :: t1 (t2 m) a -> t1 (t2 m) [a])

instance Functor (h (k m)) => Functor (FuseT h k m) where
    {-# INLINE fmap #-}
    fmap :: forall a b . (a -> b) -> FuseT h k m a -> FuseT h k m b
    fmap = coerce (fmap :: (a -> b) -> h (k m) a -> h (k m) b)

instance (Applicative (h (k f)), Applicative f) =>
  Applicative (FuseT h k f) where

    {-# INLINE pure #-}
    pure :: forall a . a -> FuseT h k f a
    pure = coerce (pure :: a -> h (k f) a)

    {-# INLINE (<*>) #-}
    (<*>) :: forall a b . FuseT h k f (a -> b) -> FuseT h k f a -> FuseT h k f b
    (<*>) = coerce ((<*>) :: h (k f) (a -> b) -> h (k f) a -> h (k f) b)

    {-# INLINE (<*) #-}
    (<*) :: forall a b . FuseT h k f a -> FuseT h k f b -> FuseT h k f a
    (<*) = coerce ((<*) :: h (k f) a -> h (k f) b -> h (k f) a)

    {-# INLINE (*>) #-}
    (*>) :: forall a b . FuseT h k f a -> FuseT h k f b -> FuseT h k f b
    (*>) = coerce ((*>) :: h (k f) a -> h (k f) b -> h (k f) b)

    {-# INLINE liftA2 #-}
    liftA2 :: forall a b c . (a -> b -> c) -> FuseT h k f a -> FuseT h k f b -> FuseT h k f c
    liftA2 = coerce (liftA2 :: (a -> b -> c) -> h (k f) a -> h (k f) b -> h (k f) c)

#if __GLASGOW_HASKELL__ <= 904
instance (MonadTrans t1, MonadTrans t2, Monad m, Monad (t1(t2 m))) =>
#else
instance (MonadTrans t1, MonadTrans t2, Monad m) =>
#endif
  Monad (FuseT t1 t2 m) where
    {-# INLINE return #-}
    return :: forall a . a -> FuseT t1 t2 m a
    return = coerce (return :: a -> t1 (t2 m) a)

    {-# INLINE (>>=) #-}
    (>>=) :: forall a b . FuseT t1 t2 m a -> (a -> FuseT t1 t2 m b) -> FuseT t1 t2 m b
    (>>=) = coerce ((>>=) :: t1 (t2 m) a -> (a -> t1 (t2 m) b) -> t1 (t2 m) b)

    {-# INLINE (>>) #-}
    (>>) :: forall a b . FuseT t1 t2 m a -> FuseT t1 t2 m b -> FuseT t1 t2 m b
    (>>) = coerce ((>>) :: t1 (t2 m) a -> t1 (t2 m) b -> t1 (t2 m) b)

#if __GLASGOW_HASKELL__ <= 904
instance (MonadTrans t1, MonadTrans t2, forall m . Monad m => Monad (t2 m)) =>
#else
instance (MonadTrans t1, MonadTrans t2) =>
#endif
  MonadTrans (FuseT t1 t2) where
    {-# INLINE lift #-}
    lift :: Monad m => m a -> FuseT t1 t2 m a
    lift x = FuseT (lift (lift x))

instance
  ( MAlgebra t1
  , MAlgebra t2
  , forall m . Monad m => Monad (t2 m)
  , Forwards (oeffs1 :\\ effs2) t2
  , Forwards effs2 t1
  , Injects (oeffs1 :\\ effs2) oeffs
  , Injects (effs2 :\\ effs1) effs2
  , Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , KnownNat (Length effs1)
  , KnownNat (Length effs2)
  , effs1  ~ IEffs t1
  , effs2  ~ IEffs t2
  , oeffs1 ~ OEffs t1
  , oeffs2 ~ OEffs t2
  , oeffs  ~ (oeffs1 :\\ effs2) `Union` oeffs2
  , effs   ~ effs1 `Union` effs2
  )
  => MAlgebra (FuseT t1 t2) where
  type IEffs (FuseT t1 t2) = (IEffs t1) `Union` (IEffs t2)
  type OEffs (FuseT t1 t2) = (OEffs t1 :\\ IEffs t2) `Union` (OEffs t2)

  {-# INLINE malg #-}
  malg :: forall m .  Monad m
    => Algebra (OEffs (FuseT t1 t2)) m
    -> Algebra (IEffs (FuseT t1 t2)) (FuseT t1 t2 m)
  malg oalg
    = unsafeCoerce @(t1 (t2 m) _) @((FuseT t1 t2) m _)
    . hunion @effs1 @effs2
        (malg @t1 (weakenAlg $
          heither @(oeffs1 :\\ effs2) @effs2
            (fwds @(oeffs1 :\\ effs2) @t2 (weakenAlg oalg))
            (malg @t2 (weakenAlg oalg))))
        (fwds @effs2 @t1 (malg @t2 (oalg . injs)))
    . unsafeCoerce @(Effs effs ((FuseT t1 t2) m) _) @(Effs effs (t1 (t2 m)) _)


instance MAlgebra (ProgT effs) where
  type IEffs (ProgT effs) = effs
  type OEffs (ProgT effs) = '[]

  {-# INLINE malg #-}
  malg :: Monad m => Algebra '[] m -> Algebra effs (ProgT effs m)
  malg _ op = ProgT (return (CallF op id return))

{-# INLINE mcall #-}
mcall :: (MAlgebra t, IEffs t ~ effs, OEffs t ~ '[], HFunctor eff, Member eff effs)
      => eff (t Identity) a -> t Identity a
mcall op = malg absurdEffs (inj op)

type Syntax t eff effs = (Member eff effs, MAlgebra t, IEffs t ~ effs, OEffs t ~ '[])

reflect :: MAlgebra (ProgT eff) => Algebra '[] Identity
                                -> (forall x . ProgT eff Identity x -> Identity (ProgT eff Identity x))
reflect _ = Identity

(!>) ::  forall effs1 effs2 oeffs1 oeffs2 t1 t2 f1 f2 effs oeffs f t m
     . ( oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2
       , Monad m
       , effs  ~ effs1 `Union` effs2
       , effs1 ~ IEffs t1
       , effs2 ~ IEffs t2
       , oeffs1 ~ OEffs t1
       , oeffs2 ~ OEffs t2
       , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2
       -- , t    ~ HRAssoc (t1 `ComposeT` t2)
       , t    ~ FuseT t1 t2
       , f    ~ RAssoc (f2 `Compose` f1)
       , forall m . Monad m => Monad (t2 m)
       , forall m . Monad m => Monad (t1 (t2 m))
       , Forwards (oeffs1 :\\ effs2) t2
       , Forwards effs2 t1
       , Injects (oeffs1 :\\ effs2) oeffs
       , Injects (effs2 :\\ effs1) effs2
       , Injects oeffs2 oeffs
       , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
       , KnownNat (Length effs1)
       , KnownNat (Length effs2)
       , MAlgebra t2
       )
    => (forall m . Monad  m => Algebra oeffs1 m -> (forall x.  t1 m x -> m (f1 x)))
    -> (forall m . Monad  m => Algebra oeffs2 m -> (forall x.  t2 m x -> m (f2 x)))
                            -> Algebra oeffs m -> (forall x.  FuseT t1 t2 m  x -> m (f x))
(run1 !> run2) oalg
    = unsafeCoerce @(m (f2 (f1 _x))) @(m (f _x))
    . run2 (oalg . injs)
    . run1 (weakenAlg @oeffs1 @((oeffs1 :\\ effs2) :++ effs2) $
        heither @(oeffs1 :\\ effs2) @effs2
          (fwds @(oeffs1 :\\ effs2) @(t2)
            (weakenAlg @(oeffs1 :\\ effs2) @oeffs oalg))
          (malg @t2 (weakenAlg @oeffs2 @oeffs oalg)))
    . unsafeCoerce @(t m _) @(t1 (t2 m) _)


toProgT :: forall effs a . Prog effs a -> ProgT effs Identity a
toProgT = eval (malg @(ProgT effs) absurdEffs)

{-# INLINE handles #-}
handles :: forall t f a
  . ( forall m . Monad m => Monad (t m)
    , MAlgebra t
    , '[] ~ OEffs t
    )
  => (Algebra '[] Identity -> (forall x . t Identity x -> Identity (f x)))
  -> t Identity a -> Apply f a
handles run
  = unsafeCoerce @(f a) @(Apply f a)
  . runIdentity
  . run absurdEffs

handle' :: forall t f a
  . ( forall m . Monad m => Monad (t m)
    , MAlgebra t
    , '[] ~ OEffs t
    )
  => (Algebra '[] Identity -> (forall x . t Identity x -> Identity (f x)))
  -> Prog (IEffs t) a -> Apply f a
handle' run
  = handles run
  . eval (malg @t absurdEffs)