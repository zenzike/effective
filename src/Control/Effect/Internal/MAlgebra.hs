{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE RoleAnnotations #-}

module Control.Effect.Internal.MAlgebra where

import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Forward
import Control.Effect.Internal.Handler

import Data.HFunctor
import Data.Functor.Identity
import Data.Functor.Compose

import Control.Monad.Trans.Class
import Control.Applicative

import GHC.Exts
import GHC.TypeLits
import Unsafe.Coerce
import Data.List.Kind
import Data.Kind (Type)
import Control.Monad.Trans.Compose
import Control.Monad

-- import Data.Reflection

-- | The reified MAlgebra type
newtype MAlgebra_ t
  = MAlgebra_
    { malg_ :: forall m . Monad m
            => Algebra (OEffs t) m
            -> Algebra (IEffs t) (t m)
    }

class Reifies (s :: Type) t | s -> t where
  reflect :: Const (MAlgebra_ t) s

data Skolem

-- Const is needed for malg'? is it really?
-- Can we make malg' :: Proxy# s -> typeOf malg_  ?

newtype Magic a r = Magic (Reifies Skolem a => Const r Skolem)

{-# INLINE reify #-}
reify :: forall t r . (forall m . Monad m => Algebra (OEffs t) m -> Algebra (IEffs t) (t m))
      -> (forall s . Reifies (s :: Type) (t :: Effect) => Const r s) -> r
reify alg k = unsafeCoerce (Magic k :: Magic t r) (MAlgebra_ alg)

reifyMAlgebra
  :: forall t r
  .  (forall m . Monad m => Algebra (OEffs t) m -> Algebra (IEffs t) (t m))
  -> (forall s . Reifies s t => Const r s)
  -> r
reifyMAlgebra malg k = unsafeCoerce (Magic k :: Magic t r) (MAlgebra_ malg)

newtype ProgX (x :: Type) t a = ProgX (t Identity a)

deriving instance (Functor (t Identity)) => Functor (ProgX x t)
deriving instance (Applicative (t Identity)) => Applicative (ProgX x t)
deriving instance (Monad (t Identity)) => Monad (ProgX x t)

withMAlgebra
  :: forall t b
  .  OEffs t ~ '[]
  => (forall (m :: Type -> Type) .  Monad m => Algebra '[] m -> Algebra (IEffs t) (t m))
  -> (MAlgebra t => b) -> b
withMAlgebra alg k
  = withDict
      @(MAlgebra t)
      @(forall (m :: Type -> Type) .  Monad m => Algebra '[] m -> Algebra (IEffs t) (t m))
      alg
      k

type Foo t = forall (m :: Type -> Type) .  Monad m => Algebra '[] m -> Algebra (IEffs t) (t m)

handleX :: forall t f a .
  ( Monad (t Identity) , Functor f, OEffs t ~ '[])
  => Handler (IEffs t) (OEffs t) t f          -- ^ Handler @h@ with no output effects
  -> (forall s . Reifies s t => ProgX s t a)  -- ^ Program @p@ with effects @effs@
  -> Apply f a
handleX (Handler hrun halg) p
  = unsafeCoerce @(f a) @(Apply f a)
  . runIdentity
  . hrun absurdEffs $ reify halg (go p)
    where
      go :: ProgX s t a -> Const (t Identity a) s
      go (ProgX p) = Const p

{-# INLINE xcall #-}
xcall :: forall x t eff effs a . (Reifies x t, MAlgebra t, IEffs t ~ effs, OEffs t ~ '[], HFunctor eff, Member eff effs)
      => eff (t Identity) a -> ProgX x t a
xcall op = ProgX @x @t (malg_ (getConst (reflect @x)) absurdEffs (inj op)) -- malg absurdEffs (inj op)

{-

It is tempting to write an class like this instead for `MAlgebra`,
to simplify the machinery:

class MAlgebra effs oeffs t where
  malg :: Monad m => Algebra offs m
                  -> Algebra effs (t m)

However, the problem is that the type of `fuse` requires that
we are able to distinguish "what came from where" in the arguments.
When we fuse `t1` and `t2`, we define `FuseT t1 t2` so that we can decompose
back to `t1` and `t2`. We would have to have something similar with
the types `effs` and `oeffs`, which will complicate the types somewhat.

-}



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
  -- , KnownNat (Length effs1)
  -- , KnownNat (Length effs2)
  , Append effs1 (effs2 :\\ effs1)
  , Append (oeffs1 :\\ effs2) effs2
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

instance (MAlgebra t1, MAlgebra t2) => MAlgebra (ComposeT t1 t2) where
  type IEffs (ComposeT t1 t2) = (IEffs t1) `Union` (IEffs t2)
  type OEffs (ComposeT t1 t2) = (OEffs t1 :\\ IEffs t2) `Union` (OEffs t2)


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


{-# INLINE (!>) #-}
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
       -- , KnownNat (Length effs1)
       -- , KnownNat (Length effs2)
       , Append (oeffs1 :\\ effs2) effs2
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


toProgT :: forall effs a . HFunctor (Effs effs) => Prog effs a -> ProgT effs Identity a
toProgT = eval (malg @(ProgT effs) absurdEffs)

{-# INLINE handles #-}
handles :: forall t f a
  . ( forall m . Monad m => Monad (t m)
    , MAlgebra t
    , '[] ~ OEffs t
    , HFunctor (Effs (IEffs t))
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
    , HFunctor (Effs (IEffs t))
    )
  => (Algebra '[] Identity -> (forall x . t Identity x -> Identity (f x)))
  -> Prog (IEffs t) a -> Apply f a
handle' run
  = handles run
  . eval (malg @t absurdEffs)

type role ProgZ nominal phantom _
type ProgZ :: Effect -> [Effect] -> Type -> Type
newtype ProgZ (t :: Effect) (effs :: [Effect]) (a :: Type) = ProgZ { unProgZ :: t Identity a }

deriving instance Functor (t Identity) => Functor (ProgZ t effs)
deriving instance Applicative (t Identity) => Applicative (ProgZ t effs)
deriving instance Monad (t Identity) => Monad (ProgZ t effs)


type role MAlgebraZ nominal nominal nominal
type MAlgebraZ :: Effect -> [Effect] -> [Effect] -> Constraint
class MAlgebraZ t effs oeffs where
  malgz :: Monad m => Algebra oeffs m
                   -> Algebra effs (t m)

{-# INLINE handleZ #-}
handleZ :: forall t f a effs .
  ( Monad (t Identity) , Functor f )
  => Handler effs '[] t f
  -> (MAlgebraZ t effs '[] => ProgZ t effs a)
  -> Apply f a
handleZ (Handler hrun halg) p
  = unsafeCoerce @(Identity (f a)) @(Apply f a)
  . hrun absurdEffs
  . withMAlgebraZ halg
  $ (coerce `asTypeOf` unProgZ) p

{-# INLINE withMAlgebraZ #-}
withMAlgebraZ
  :: forall t effs b
  .  (forall (m :: Type -> Type) . Monad m => Algebra '[] m -> Algebra effs (t m))
  -> (MAlgebraZ t effs '[] => b) -> b
withMAlgebraZ alg k
  = withDict
      @(MAlgebraZ t effs '[])
      @(forall (m :: Type -> Type) .  Monad m => Algebra '[] m -> Algebra effs (t m))
      (inline alg)
      k

{-# INLINE zcall #-}
zcall :: forall t eff effs (a :: Type) . (Functor (t Identity), HFunctor eff, Member eff effs, MAlgebraZ t effs '[])
  => eff (ProgZ t effs) a -> ProgZ t effs a
zcall op = ProgZ (malgz @t @effs @'[] absurdEffs (coerce' `asTypeOf` (hmap unProgZ) $ inj @eff @effs op))
  where coerce' :: Effs effs (ProgZ t effs) a -> Effs effs (t Identity) a
        coerce' = hmap coerceT

coerceT :: ProgZ t effs a -> t Identity a
coerceT = coerce

coerceT' :: forall (t :: Effect) (effs :: [Effect]) (a :: Type)
         . ( Functor (t Identity)
         , HFunctor (Effs effs) )
         => Effs effs (ProgZ t effs) a -> Effs effs (t Identity) a
coerceT' = hmap coerce

{-# INLINE zcall' #-}
zcall'
  :: forall t eff effs (a :: Type)
  . ( Monad (t Identity), HFunctor eff, Member eff effs, MAlgebraZ t effs '[])
  => eff (ProgZ t effs) (ProgZ t effs a) -> ProgZ t effs a
-- zcall' op = ProgZ (join (malgz @t @effs @'[] absurdEffs (unsafeCoerce (inj @eff @effs op))))
zcall' op = ProgZ (join (malgz @t @effs @'[] absurdEffs (unsafeCoerce (inj @eff @effs op))))