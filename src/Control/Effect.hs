{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect where

import Data.Kind ( Type, Constraint )

import Data.List.Kind
import Data.Functor.Identity
import Data.Functor.Composes
import Data.HFunctor
import Data.HFunctor.HCompose
import Control.Monad.Trans.Identity


import Control.Monad ( join, ap, liftM )
import qualified Control.Monad.Graded as Graded
import Control.Monad.Trans.Class

type Effect = (Type -> Type) -> (Type -> Type)
type Signature = Type -> Type

type Eff :: Signature -> Effect
data Eff sig f x
  = Alg (sig x)
  | Scp (sig (f x))
  deriving Functor

instance Functor sig => HFunctor (Eff sig) where
  hmap h (Alg x) = Alg x
  hmap h (Scp x) = Scp (fmap h x)

type Effs :: [Signature] -> Effect
data Effs sigs f a where
  Eff  :: Functor sig => Eff sig f a -> Effs (sig ': sigs) f a
  Effs :: Effs sigs f a -> Effs (sig ': sigs) f a

instance Functor f => Functor (Effs sigs f) where
  fmap f (Eff x)  = Eff (fmap f x)
  fmap f (Effs x) = Effs (fmap f x)

instance HFunctor (Effs sigs) where
  hmap h (Eff x)  = Eff (hmap h x)
  hmap h (Effs x) = Effs (hmap h x)

absurdEffs :: Effs '[] f x -> a
absurdEffs x = case x of {}

data Nat = Z | S Nat

type SNat :: Nat -> Type
data SNat n = SNat
-- injecting/projecting at a specified position SNat n

-- Find an index of an element in a `list'
-- The element must exist
-- This closed type family disambiguates otherwise overlapping
-- instances
type family ElemIndex (x :: a) (xs :: [a]) :: Nat where
  ElemIndex x (x ': xs) = Z
  ElemIndex x (_ ': xs) = S (ElemIndex x xs)

class (Functor sig, HFunctor (Effs sigs)) => Member' sig sigs (n :: Nat) where
  inj' :: SNat n -> Eff sig f a -> Effs sigs f a
  prj' :: SNat n -> Effs sigs f a -> Maybe (Eff sig f a)


instance (Functor sig, (sigs' ~ (sig ': sigs))) => Member' sig sigs' Z where
  inj' :: (Functor sig, sigs' ~ (sig : sigs)) => SNat Z -> Eff sig f a -> Effs sigs' f a
  inj' _ = Eff

  prj' :: (Functor sig, sigs' ~ (sig : sigs)) => SNat Z -> Effs sigs' f a -> Maybe (Eff sig f a)
  prj' _ (Eff x) = Just x
  prj' _ _        = Nothing

instance (sigs' ~ (sig' ': sigs), Functor sig, Member' sig sigs n) => Member' sig sigs' (S n) where
  inj' _ = Effs . inj' (SNat :: SNat n)

  prj' _ (Eff _)  = Nothing
  prj' _ (Effs x) = prj' (SNat :: SNat n) x

type Member :: Signature -> [Signature] -> Constraint
class (Member' sig sigs (ElemIndex sig sigs)) => Member sig sigs where
  inj :: Eff sig f a -> Effs sigs f a
  prj :: Effs sigs m a -> Maybe (Eff sig m a)

instance (Member' sig sigs (ElemIndex sig sigs)) => Member sig sigs where
  inj = inj' (SNat :: SNat (ElemIndex sig sigs))
  prj = prj' (SNat :: SNat (ElemIndex sig sigs))

type family Members (xs :: [Signature]) (xys :: [Signature]) :: Constraint where
  Members '[] xys       = ()
  Members (x ': xs) xys = (Member x xys, Members xs xys, Injects (x ': xs) xys)

-- Injects xs ys means that all of xs is in xys
-- Some other effects may be in xys, so xs <= ys
type  Injects :: [Signature] -> [Signature] -> Constraint
class Injects xs xys where
  injs :: Effs xs f a -> Effs xys f a

instance Injects '[] xys where
  injs :: Effs '[] f a -> Effs xys f a
  injs = absurdEffs

instance (Member x xys, Injects xs xys)
  => Injects (x ': xs) xys where
  injs (Eff x)  = inj x
  injs (Effs x) = injs x

hunion :: forall xs ys f a b
  . ( Append xs (ys :\\ xs)
  ,   Injects (ys :\\ xs) ys )
  => (Effs xs f a -> b) -> (Effs ys f a -> b) -> (Effs (xs `Union` ys) f a -> b)
hunion xalg yalg = heither @xs @(ys :\\ xs) xalg (yalg . injs)

type  Append :: [Signature] -> [Signature] -> Constraint
class Append xs ys where
  heither :: (Effs xs h a -> b) -> (Effs ys h a -> b) -> (Effs (xs :++ ys) h a -> b)

  hinl :: Effs xs f a -> Effs (xs :++ ys) f a
  hinr :: Effs ys f a -> Effs (xs :++ ys) f a

  houtl :: Effs (xs :++ ys) f a -> Maybe (Effs xs f a)
  houtr :: Effs (xs :++ ys) f a -> Maybe (Effs ys f a)

instance Append '[] ys where
  heither :: (Effs '[] f a -> b) -> (Effs ys f a -> b) -> (Effs ('[] :++ ys) f a -> b)
  heither xalg yalg = yalg

  hinl :: Effs '[] f a -> Effs ys f a
  hinl = absurdEffs

  hinr :: Effs ys f a -> Effs ys f a
  hinr = id

  houtl :: Effs ys f a -> Maybe (Effs '[] f a)
  houtl = const Nothing

  houtr :: Effs ys f a -> Maybe (Effs ys f a)
  houtr = Just

instance Append xs ys => Append (x ': xs) ys where
  heither :: (Effs (x : xs) f a -> b) -> (Effs ys f a -> b) -> Effs ((x : xs) :++ ys) f a -> b
  heither xalg yalg (Eff x)  = xalg (Eff x)
  heither xalg yalg (Effs x) = heither (xalg . Effs) yalg x

  hinl :: Effs (x : xs) f a -> Effs ((x : xs) :++ ys) f a
  hinl (Eff x)  = Eff x
  hinl (Effs x) = Effs (hinl @xs @ys x)

  hinr :: Effs ys f a -> Effs ((x : xs) :++ ys) f a
  hinr = Effs . hinr @xs @ys

  houtl :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs (x ': xs) f a)
  houtl (Eff x)  = Just (Eff x)
  houtl (Effs x) = fmap Effs (houtl @xs @ys x)

  houtr :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs ys f a)
  houtr (Eff x)  = Nothing
  houtr (Effs x) = houtr @xs @ys x

joinAlg :: forall sig1 sig2 oeff t m .
  ( Monad m, Append sig1 sig2 )
  => ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs sig1 (t m) x -> t m x))
  -> ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs sig2 (t m) x -> t m x))
  -> ((forall x . Effs oeff m x -> m x) ->
     (forall x. Effs (sig1 :++ sig2) (t m) x -> t m x))
joinAlg falg galg oalg =
  heither @sig1 @sig2 (falg oalg) (galg oalg)

---------------------------------------
type Prog' sig a = forall sig' . Members sig sig' => Prog sig' a
data Prog (sigs :: [Signature]) a where
  Return :: a -> Prog sigs a
  Call   :: (Effs sigs) (Prog sigs) (Prog sigs a) -> Prog sigs a

instance Functor (Prog sigs) where
  fmap :: (a -> b) -> Prog sigs a -> Prog sigs b
  fmap = liftM

instance Applicative (Prog effs) where
  pure :: a -> Prog effs a
  pure  = Return

  (<*>) :: Prog effs (a -> b) -> Prog effs a -> Prog effs b
  (<*>) = ap

instance Monad (Prog effs) where
  Return x >>= f = f x
  Call op  >>= f = Call (fmap (>>= f) op)

instance Graded.GradedMonad Prog where
  type Unit Prog = '[] :: [Signature]
  type Plus Prog effs effs' = Union effs effs'
  type Inv Prog effs effs' =
    ( Injects effs (Union effs effs')
    , Injects effs' (Union effs effs'))

  return = Return
  (>>=) :: forall (i :: [Signature]) (j :: [Signature]) a b.
           Graded.Inv Prog i j =>
           Prog i a -> (a -> Prog j b) -> Prog (Graded.Plus Prog i j) b
  (Return x)  >>= f = weakenProg (f x)
  (Call op)   >>= f = Call ((hmap weakenProg . injs @i @(Union i j) . fmap (Graded.>>= f)) op)


weakenProg :: forall effs effs' a
  .  Injects effs effs'
  => Prog effs a -> Prog effs' a
weakenProg (Return x) = Return x
weakenProg (Call op)   =
    Call ( injs @effs @effs'
         . hmap (weakenProg @effs @effs')
         . fmap (weakenProg @effs @effs')
         $ op )

-- Universal property from initial monad `Prog sig a` equipped with
-- `sig m -> m`
eval :: Monad m
  => (forall x . Effs effs m x -> m x)
  -> Prog effs a -> m a
eval halg (Return x) = return x
eval halg (Call op)  =
  join (halg ((fmap (eval halg) . hmap (eval halg)) op))

-- Universal property from the GADT, Functorial Algebra
fold :: Functor f
  => (forall x . (Effs effs f) (f x) -> f x)
  -> (forall x . x -> f x)
  -> Prog effs a -> f a
fold falg gen (Return x) = gen x
fold falg gen (Call op)  =
  falg ((fmap (fold falg gen) . hmap (fold falg gen)) op)

injCall :: Member sub sup => Eff sub (Prog sup) (Prog sup a) -> Prog sup a
injCall = Call . inj

prjCall :: Member sub sup => Prog sup a -> Maybe (Eff sub (Prog sup) (Prog sup a))
prjCall (Call op) = prj op
prjCall _         = Nothing

progAlg :: Effs sig (Prog sig) a -> Prog sig a
progAlg = Call . fmap return

type Handler
  :: [Signature]                          -- effs  : input effects
  -> [Signature]                          -- oeffs : output effects
  -> [Type -> Type]                       -- f     : carrier type
  -> Type
data Handler effs oeffs fs
  =  forall t . (HFunctor t, MonadTrans t)
  => Handler (Handler' effs oeffs t fs)

type Handler'
  :: [Signature]                          -- effs  : input effects
  -> [Signature]                          -- oeffs : output effects
  -> ((Type -> Type) -> (Type -> Type))   -- t     : monad transformer
  -> [Type -> Type]                       -- f     : carrier type
  -> Type
data Handler' effs oeffs t fs =
  Handler'
  { run  :: forall m . Monad m
         => (forall x . Effs oeffs m x -> m x)
         -> (forall x . t m x -> m (Comps fs x))

  , malg :: forall m . Monad m
         => (forall x . Effs oeffs m x -> m x)
         -> (forall x . Effs effs (t m) x -> t m x)

  , mfwd :: forall m sig . Monad m
         => (forall x . Effs sig m x -> m x)
         -> (forall x . Effs sig (t m) x -> t m x)
  }

handler
  :: (MonadTrans t, HFunctor t, Functor f)
  => (forall m a . Monad m => t m a -> m (f a))
  -> (forall m . Monad m
    => (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs effs (t m) x -> t m x))
  -> (forall m sigs . Monad m
    => (forall x . Effs sigs m x -> m x)
    -> (forall x . Effs sigs (t m) x -> t m x))
  -> Handler effs oeffs '[f]
handler run malg mfwd = Handler (Handler' (const (fmap comps . run)) malg mfwd)


-- TODO: A better error message for unsafePrj
interpret
  :: forall eff effs oeffs
  .  Member eff effs
  => (forall m x . Eff eff m x -> Prog oeffs x)
  -> Handler effs oeffs '[]
interpret f = interpret' (\oalg -> eval oalg . f . unsafePrj)
  where
    unsafePrj :: Effs effs m x -> Eff eff m x
    unsafePrj x = case prj x of Just y -> y

interpret'
  :: (forall m . Monad m
     => (forall x . Effs oeffs m x -> m x)
     -> (forall x . Effs effs m x -> m x))
  -> Handler effs oeffs '[]
interpret' alg
  = Handler $ Handler'
      (const (\(IdentityT mx) -> fmap CNil mx))
      (\oalg -> IdentityT . alg oalg . hmap runIdentityT)
      (\alg  -> IdentityT . alg . hmap runIdentityT)

fuse :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 effs oeffs .
  ( All Functor fs1, All Functor fs2, All Functor (fs2 :++ fs1)
  , Expose fs2
  , Append effs1 (effs2 :\\ effs1)
  , Append (oeffs1 :\\ effs2) (oeffs2 :\\ (oeffs1 :\\ effs2))
  , Append (oeffs1 :\\ effs2) effs2
  , Append (oeffs1 :\\ effs2) oeffs2
  , Injects (oeffs1 :\\ effs2) oeffs, Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (effs2 :\\ effs1) effs2
  , effs  ~ effs1 `Union` effs2
  , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2 )
  => Handler effs1 oeffs1 fs1
  -> Handler effs2 oeffs2 fs2
  -> Handler (effs1 `Union` effs2) ((oeffs1 :\\ effs2) `Union` oeffs2 ) (fs2 :++ fs1)
fuse (Handler h1) (Handler h2) = Handler (fuse' h1 h2)

fuse' :: forall effs1 effs2 oeffs1 oeffs2 t1 t2 fs1 fs2 effs oeffs .
  ( All Functor (fs2 :++ fs1)
  , MonadTrans t1
  , MonadTrans t2
  , HFunctor t1
  , HFunctor t2
  , Expose fs2
  , Append effs1 (effs2 :\\ effs1)
  , Append (oeffs1 :\\ effs2) (oeffs2 :\\ (oeffs1 :\\ effs2))
  , Append (oeffs1 :\\ effs2) effs2
  , Append (oeffs1 :\\ effs2) oeffs2
  , Injects (oeffs1 :\\ effs2) oeffs, Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (effs2 :\\ effs1) effs2
  , effs  ~ effs1 `Union` effs2
  , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2 )
  => Handler' effs1 oeffs1 t1 fs1
  -> Handler' effs2 oeffs2 t2 fs2
  -> Handler' effs oeffs (HCompose t1 t2) (fs2 :++ fs1)
fuse' (Handler' run1 malg1 mfwd1) (Handler' run2 malg2 mfwd2) =
  Handler' run malg mfwd where
    run :: forall m . Monad m
        => (forall x. Effs oeffs m x -> m x)
        -> (forall x. HCompose t1 t2 m x -> m (Comps (fs2 :++ fs1) x))
    run oalg
      = fmap (unexpose @fs2 @fs1)
      . run2 (oalg . injs)
      . run1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @(effs2)
          (mfwd2 (weakenAlg oalg))
          (malg2 (weakenAlg oalg)))
      . getHCompose

    malg :: forall m . Monad m
      => (forall x . Effs oeffs m x -> m x)
      -> (forall x. Effs effs (HCompose t1 t2 m) x -> HCompose t1 t2 m x)
    malg oalg
      = HCompose
      . hunion @effs1 @effs2
          (malg1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @effs2
                                (mfwd2 (weakenAlg oalg))
                                (malg2 (weakenAlg oalg))))
          (mfwd1 (malg2 (oalg . injs)))
      . hmap getHCompose

    mfwd
      :: forall m sig . Monad m
      => (forall x. Effs sig m x -> m x)
      -> forall x. Effs sig (HCompose t1 t2 m) x -> HCompose t1 t2 m x
    mfwd alg
      = HCompose
      . mfwd1 (mfwd2 alg)
      . hmap getHCompose

(<&>) :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 effs oeffs .
  ( All Functor fs1, All Functor fs2, All Functor (fs2 :++ fs1)
  , Expose fs2
  , Append effs1 (effs2 :\\ effs1)
  , Append (oeffs1 :\\ effs2) (oeffs2 :\\ (oeffs1 :\\ effs2))
  , Append (oeffs1 :\\ effs2) effs2
  , Append (oeffs1 :\\ effs2) oeffs2
  , Injects (oeffs1 :\\ effs2) oeffs, Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (effs2 :\\ effs1) effs2
  , effs  ~ effs1 `Union` effs2
  , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2 )
  => Handler effs1 oeffs1 fs1
  -> Handler effs2 oeffs2 fs2
  -> Handler (effs1 `Union` effs2) ((oeffs1 :\\ effs2) `Union` oeffs2 ) (fs2 :++ fs1)
(<&>) = fuse

pipe :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 oeffs .
  ( All Functor (fs2 :++ fs1)
  , Expose fs2
  , oeffs ~ ((oeffs1 :\\ effs2) `Union` oeffs2)
  , Append (oeffs1 :\\ effs2) effs2
  , Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (oeffs1 :\\ effs2) oeffs )
  => Handler effs1 oeffs1 fs1
  -> Handler effs2 oeffs2 fs2
  -> Handler effs1 ((oeffs1 :\\ effs2) `Union` oeffs2) (fs2 :++ fs1)
pipe (Handler h1) (Handler h2) = Handler (pipe' h1 h2)

pipe' :: forall effs1 effs2 oeffs1 oeffs2 t1 t2 fs1 fs2 oeffs .
  ( All Functor (fs2 :++ fs1)
  , MonadTrans t1
  , MonadTrans t2
  , HFunctor t1
  , HFunctor t2
  , Expose fs2
  , oeffs ~ ((oeffs1 :\\ effs2) `Union` oeffs2)
  , Append (oeffs1 :\\ effs2) effs2
  , Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (oeffs1 :\\ effs2) oeffs )
  => Handler' effs1 oeffs1 t1 fs1
  -> Handler' effs2 oeffs2 t2 fs2
  -> Handler' effs1 ((oeffs1 :\\ effs2) `Union` oeffs2) (HCompose t1 t2) (fs2 :++ fs1)
pipe' (Handler' run1 malg1 mfwd1) (Handler' run2 malg2 mfwd2) =
  Handler' run malg mfwd where
  run  :: forall m . Monad m
    => (forall x . Effs ((oeffs1 :\\ effs2) `Union` oeffs2) m x -> m x)
    -> (forall x . HCompose t1 t2 m x -> m (Comps (fs2 :++ fs1) x))
  run oalg
    = fmap (unexpose @fs2 @fs1)
    . run2 (oalg . injs)
    . run1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @(effs2)
        (mfwd2 (weakenAlg oalg))
        (malg2 (weakenAlg oalg)))
    . getHCompose

  malg :: forall m . Monad m
    => (forall x . Effs ((oeffs1 :\\ effs2) `Union` oeffs2) m x -> m x)
    -> (forall x . Effs effs1 (HCompose t1 t2 m) x -> HCompose t1 t2  m x)
  malg oalg
    = HCompose
    . (malg1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @effs2
                            (mfwd2 (weakenAlg oalg))
                            (malg2 (weakenAlg oalg))))
    . hmap getHCompose

  mfwd
    :: forall m sig . Monad m
    => (forall x. Effs sig m x -> m x)
    -> forall x. Effs sig (HCompose t1 t2 m) x -> HCompose t1 t2 m x
  mfwd alg
    = HCompose
    . mfwd1 (mfwd2 alg)
    . hmap getHCompose

pass :: forall sig effs oeffs fs .
  ( All Functor fs
  , Append effs (sig :\\ effs)
  , Append (oeffs :\\ sig) sig
  , Append (oeffs :\\ sig) (sig :\\ (oeffs :\\ sig))
  , Injects sig ((oeffs :\\ sig) :++ (sig :\\ (oeffs :\\ sig)))
  , Injects oeffs ((oeffs :\\ sig) :++ sig)
  , Injects (oeffs :\\ sig) ((oeffs :\\ sig) :++ (sig :\\ (oeffs :\\ sig)))
  , Injects (sig :\\ effs) sig)
  => Handler effs oeffs fs
  -> Handler (effs `Union` sig) ((oeffs :\\ sig) `Union` sig) fs
pass h = fuse h (forward @sig)


forward :: Handler effs effs '[]
forward = Handler $ Handler'
  (const (\(IdentityT mx) -> fmap CNil mx))
  (\oalg -> IdentityT . oalg . hmap runIdentityT)
  (\alg  -> IdentityT . alg . hmap runIdentityT)

handle :: forall ieffs fs a .
  ( Recompose fs )
  => Handler ieffs '[] fs
  -> Prog ieffs a -> (Composes fs a)
handle (Handler h) p = handle' h p

handle' :: forall ieffs t fs a .
  ( Monad (t Identity)
  , Recompose fs )
  => Handler' ieffs '[] t fs
  -> Prog ieffs a -> Composes fs a
handle' (Handler' run malg mfwd)
  = runIdentity
  . fmap @Identity (recompose @fs @a)
  . run @Identity (absurdEffs . injs)
  . eval (malg (absurdEffs . injs))

handleWith :: forall ieffs oeffs xeffs m fs a .
  ( Monad m
  , Recompose fs
  , Append ieffs (xeffs :\\ ieffs)
  , Injects oeffs xeffs
  , Injects (xeffs :\\ ieffs) xeffs
  )
  => (forall x. Effs xeffs m x -> m x)
  -> Handler ieffs oeffs fs
  -> Prog (ieffs `Union` xeffs) a -> m (Composes fs a)
handleWith xalg (Handler (Handler' run malg mfwd))
  = fmap @m (recompose @fs @a)
  . run @m (xalg . injs)
  . eval (hunion @ieffs @xeffs (malg (xalg . injs)) (mfwd xalg))

-- handleOne
--   :: (Monad (HComps ts (Prog oeffs)), Recompose fs)
--   => Handler effs ts fs oeffs -> Prog effs a -> Prog oeffs (Composes fs a)
-- handleOne (Handler run malg mfwd)
--   = fmap recompose . run (Call . fmap return) . eval (malg (Call . fmap return))
-- 
-- handleOneWith
--   :: (Monad (HComps ts (Prog oeffs)), Recompose fs)
--   => (forall x . Effs oeffs (Prog oeffs) x -> Prog oeffs x)
--   -> Handler effs ts fs oeffs -> Prog effs a -> Prog oeffs (Composes fs a)
-- handleOneWith xalg (Handler run malg mfwd)
--   = fmap recompose . run xalg . eval (malg xalg)
-- 
-- handleSome
--   :: forall sig eff oeffs ts fs a
--   .  (Injects oeffs (oeffs :++ sig), Injects sig (oeffs :++ sig), Append eff sig
--   ,  Monad (HComps ts (Prog (oeffs :++ sig))), Recompose fs)
--   => Handler eff ts fs oeffs -> Prog (eff :++ sig) a -> Prog (oeffs :++ sig) (Composes fs a)
-- handleSome (Handler run malg mfwd)
--   = fmap recompose
--   . run (Call . injs . fmap return)
--   . eval (heither @eff @sig (malg @(Prog (oeffs :++ sig)) (Call . injs . fmap return))
--                             (mfwd @(Prog (oeffs :++ sig)) (Call . injs . fmap return)))



weaken
  :: forall ieffs ieffs' oeffs oeffs' ts fs
  . ( Injects ieffs ieffs'
    , Injects oeffs oeffs'
    )
  => Handler ieffs' oeffs fs
  -> Handler ieffs oeffs' fs
weaken (Handler (Handler' run malg mfwd))
  = Handler (Handler' (\oalg -> run (oalg . injs)) (\oalg -> malg (oalg . injs) . injs) mfwd)

hide
  :: forall sigs effs oeffs f
  .  (Injects (effs :\\ sigs) effs, Injects oeffs oeffs)
  => Handler effs oeffs f -> Handler (effs :\\ sigs) oeffs f
hide h = weaken h
-- (\/)
--   :: forall effs1 effs2 ts fs oeffs
--   . (Append effs1 effs2)
--   => Handler effs1 ts fs oeffs
--   -> Handler effs2 ts fs oeffs
--   -> Handler (effs1 :++ effs2) ts fs oeffs
-- Handler run1 malg1 mfwd1 \/ Handler run2 malg2 mfwd2
--   = Handler run1 (\oalg -> heither (malg1 oalg) (malg2 oalg)) mfwd1


-- transform
--   :: forall effs ts
--   . ( All MonadTrans ts, Functor (HComposes ts Identity) )
--   => Handler effs ts '[HComposes ts Identity] effs
-- transform = Handler run malg mfwd where
--   run  :: forall m . Monad m
--        => (forall x . Effs effs m x -> m x)
--        -> (forall x . HComps ts m x -> m (Comps '[HComposes ts Identity] x))
--   run alg (HNil x)  = fmap (CCons . Identity . CNil) x
--   run alg (HCons x) = (fmap (CCons . undefined . fmap CNil) . return @m) x
-- 
--   malg :: forall m . Monad m
--        => (forall x . Effs effs m x -> m x)
--        -> (forall x . Effs effs (HComps ts m) x -> HComps ts m x)
--   malg = undefined
-- 
--   mfwd :: forall m sig . Monad m
--        => (forall x . Effs sig m x -> m x)
--        -> (forall x . Effs sig (HComps ts m) x -> HComps ts m x)
--   mfwd = undefined

-- A second way:
-- fuse the handler with a trivial one that targets
-- all of xeffs. I expect these to be equivalent.

weakenAlg
  :: forall eff eff' m x . (Injects eff eff')
  => (Effs eff' m x -> m x)
  -> (Effs eff  m x -> m x)
weakenAlg alg = alg . injs




