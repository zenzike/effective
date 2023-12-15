{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE IncoherentInstances #-}

module Control.Effects where

import Data.Kind ( Type, Constraint )

import Data.List.Kind
import Data.Functor.Identity
import Data.Functor.Composes
import Data.HFunctor
import Data.HFunctor.HCompose
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Cont


import Control.Monad ( join, ap, liftM )
import qualified Control.Monad.Graded as Graded
import Control.Monad.Trans.Class

type EitherAlgScp :: Effect -> Constraint
class EitherAlgScp sig where
  type EAlgScp sig :: Type -> Type
  eproject :: sig f a -> Either (Algebraic (EAlgScp sig) f a) (Scoped (EAlgScp sig) f a)

-- instance {-# INCOHERENT #-} (JustAlg sig) => EitherAlgScp sig where
--   type EAlgScp sig = JAlg sig
--   eproject = Left . Algebraic

-- instance {-# OVERLAPS #-} (JustScp sig) => EitherAlgScp sig where
--   type EAlgScp sig = JScp sig
--   eproject = Right

type JustAlg :: Effect -> Constraint
class JustAlg sig where
  type JAlg sig :: Type -> Type
  aproject :: sig f a -> (Algebraic (JAlg sig) f a)

instance JustAlg (Algebraic lsig) where
  type JAlg (Algebraic lsig) = lsig
  aproject = id

type JustScp :: Effect -> Constraint
class JustScp sig where
  type JScp sig :: Type -> Type
  sproject :: sig f a -> Scoped (JScp sig) f a

instance JustScp (Scoped lsig) where
  type JScp (Scoped lsig) = lsig
  sproject = id

data Lan g h a where
  Lan :: (g b -> a) -> h b -> Lan g h a

data FusedSig sig m a where
  FusedSig :: (forall x . ctx (n x) -> m (ctx x))
           -> ctx ()
           -> sig n a
           -> FusedSig sig m a
-- FusedSig sig m a -> m a
--  is in bijection with
-- alg :: forall ctx n . (forall x . ctx (n x) -> m (ctx x)) -> ctx () -> sig n a -> m (ctx a)
class Fused sig where
  type JFus sig :: Effect
  fproject :: sig f a -> FusedSig (JFus sig) f a


type Family = Effect -> Constraint


type Effect = (Type -> Type) -> (Type -> Type)
type Signature = Type -> Type

newtype Algebraic lsig f x = Algebraic (lsig x)
newtype Scoped    lsig f x = Scoped (lsig (f x))

type Eff :: Signature -> Effect
data Eff sig f x
  = Alg (sig x)
  | Scp (sig (f x))
  deriving Functor

instance Functor sig => HFunctor (Eff sig) where
  hmap h (Alg x) = Alg x
  hmap h (Scp x) = Scp (fmap h x)

type Effs :: [Effect] -> Effect
data Effs sigs f a where
  Eff  :: HFunctor sig => sig f a -> Effs (sig ': sigs) f a
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

type Member' :: Effect -> [Effect] -> Nat -> Constraint
class (HFunctor sig, HFunctor (Effs sigs)) => Member' sig sigs (n :: Nat) where
  inj' :: SNat n -> sig f a -> Effs sigs f a
  prj' :: SNat n -> Effs sigs f a -> Maybe (sig f a)


instance (HFunctor sig, (sigs' ~ (sig ': sigs))) => Member' sig sigs' Z where
  inj' :: (HFunctor sig, sigs' ~ (sig : sigs)) => SNat Z -> sig f a -> Effs sigs' f a
  inj' _ = Eff

  prj' :: (HFunctor sig, sigs' ~ (sig ': sigs)) => SNat Z -> Effs sigs' f a -> Maybe (sig f a)
  prj' _ (Eff x) = Just x
  prj' _ _        = Nothing

instance (sigs' ~ (sig' ': sigs), HFunctor sig, Member' sig sigs n) => Member' sig sigs' (S n) where
  inj' _ = Effs . inj' (SNat :: SNat n)

  prj' _ (Eff _)  = Nothing
  prj' _ (Effs x) = prj' (SNat :: SNat n) x

type Member :: Effect -> [Effect] -> Constraint
class (Member' sig sigs (ElemIndex sig sigs)) => Member sig sigs where
  inj :: sig f a -> Effs sigs f a
  prj :: Effs sigs m a -> Maybe (sig m a)

instance (Member' sig sigs (ElemIndex sig sigs)) => Member sig sigs where
  inj = inj' (SNat :: SNat (ElemIndex sig sigs))
  prj = prj' (SNat :: SNat (ElemIndex sig sigs))

type family Members (xs :: [Effect]) (xys :: [Effect]) :: Constraint where
  Members '[] xys       = ()
  Members (x ': xs) xys = (Member x xys, Members xs xys, Injects (x ': xs) xys)

-- Injects xs ys means that all of xs is in xys
-- Some other effects may be in xys, so xs <= ys
type  Injects :: [Effect] -> [Effect] -> Constraint
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

type  Append :: [Effect] -> [Effect] -> Constraint
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

type Prog' sig a = forall sig' . Members sig sig' => Prog sig' a
data Prog (sigs :: [Effect]) a where
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

injCall :: Member sub sup => sub (Prog sup) (Prog sup a) -> Prog sup a
injCall = Call . inj

prjCall :: Member sub sup => Prog sup a -> Maybe (sub (Prog sup) (Prog sup a))
prjCall (Call op) = prj op
prjCall _         = Nothing

progAlg :: Effs sig (Prog sig) a -> Prog sig a
progAlg = Call . fmap return

type Handler
  :: [Effect]                             -- effs  : input effects
  -> [Effect]                             -- oeffs : output effects
  -> [Type -> Type]                       -- f     : carrier type
  -> Family                               -- fam   : forwarding family
  -> Type
data Handler effs oeffs fs fam
  =  forall t . (HFunctor t, MonadTrans t)
  => Handler (Handler' effs oeffs t fs fam)

type Handler'
  :: [Effect]                             -- effs  : input effects
  -> [Effect]                             -- oeffs : output effects
  -> ((Type -> Type) -> (Type -> Type))   -- t     : monad transformer
  -> [Type -> Type]                       -- f     : carrier type
  -> Family                               -- fam   : forwarding family
  -> Type
data Handler' effs oeffs t fs fam =
  Handler'
  { hrun :: forall m . Monad m
         => (forall x . Effs oeffs m x -> m x)
         -> (forall x . t m x -> m (Comps fs x))

  , halg :: forall m . Monad m
         => (forall x . Effs oeffs m x -> m x)
         -> (forall x . Effs effs (t m) x -> t m x)

  , hfwd :: forall m (sig :: Effect)
         . ( Monad m, fam sig , HFunctor sig )
         => (forall x . sig m x -> m x)
         -> (forall x . sig (t m) x -> t m x)
  }


handler
  :: (MonadTrans t, HFunctor t, Functor f)
  => (forall m a . Monad m => t m a -> m (f a))
  -> (forall m . Monad m
    => (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs effs (t m) x -> t m x))
  -> (forall m sigs . ( Monad m, fam sigs )
    => (forall x . sigs m x -> m x)
    -> (forall x . sigs (t m) x -> t m x))
  -> Handler effs oeffs '[f] fam
handler run malg mfwd = Handler (Handler' (const (fmap comps . run)) malg mfwd)


-- TODO: A better error message for unsafePrj
interpret
  :: forall eff effs oeffs fam
  .  Member eff effs
  => (forall m x . eff m x -> Prog oeffs x)
  -> Handler effs oeffs '[] fam
interpret f = interpret' (\oalg -> eval oalg . f . unsafePrj)
  where
    unsafePrj :: Effs effs m x -> eff m x
    unsafePrj x = case prj x of Just y -> y

interpret'
  :: (forall m . Monad m
     => (forall x . Effs oeffs m x -> m x)
     -> (forall x . Effs effs m x -> m x))
  -> Handler effs oeffs '[] fam
interpret' alg
  = Handler $ Handler'
      (const (\(IdentityT mx) -> fmap CNil mx))
      (\oalg -> IdentityT . alg oalg . hmap runIdentityT)
      (\alg  -> IdentityT . alg . hmap runIdentityT)

fuse :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 effs oeffs fam .
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
  , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2 
  , fam (Effs (oeffs1 :\\ effs2))
  , fam (Effs effs2))
  => Handler effs1 oeffs1 fs1 fam
  -> Handler effs2 oeffs2 fs2 fam
  -> Handler (effs1 `Union` effs2) ((oeffs1 :\\ effs2) `Union` oeffs2 ) (fs2 :++ fs1) fam
fuse (Handler h1) (Handler h2) = Handler (fuse' h1 h2)

fuse' :: forall effs1 effs2 oeffs1 oeffs2 t1 t2 fs1 fs2 effs oeffs fam .
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
  , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2 
  , fam (Effs (oeffs1 :\\ effs2))
  , fam (Effs effs2))
  => Handler' effs1 oeffs1 t1 fs1 fam
  -> Handler' effs2 oeffs2 t2 fs2 fam
  -> Handler' effs oeffs (HCompose t1 t2) (fs2 :++ fs1) fam
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
      :: forall m sig . ( Monad m , fam sig, HFunctor sig )
      => (forall x. sig m x -> m x)
      -> forall x. sig (HCompose t1 t2 m) x -> HCompose t1 t2 m x
    mfwd alg
      = HCompose
      . mfwd1 (mfwd2 alg)
      . hmap getHCompose

(<&>) :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 effs oeffs fam .
  ( All Functor fs1, All Functor fs2, All Functor (fs2 :++ fs1)
  , Expose fs2
  , Append effs1 (effs2 :\\ effs1)
  , Append (oeffs1 :\\ effs2) (oeffs2 :\\ (oeffs1 :\\ effs2))
  , Append (oeffs1 :\\ effs2) effs2
  , Append (oeffs1 :\\ effs2) oeffs2
  , Injects (oeffs1 :\\ effs2) oeffs, Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (effs2 :\\ effs1) effs2
  , fam (Effs (oeffs1 :\\ effs2))
  , fam (Effs effs2) 
  , effs  ~ effs1 `Union` effs2
  , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2 )
  => Handler effs1 oeffs1 fs1 fam
  -> Handler effs2 oeffs2 fs2 fam
  -> Handler (effs1 `Union` effs2) ((oeffs1 :\\ effs2) `Union` oeffs2 ) (fs2 :++ fs1) fam
(<&>) = fuse

pipe :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 oeffs fam .
  ( All Functor (fs2 :++ fs1)
  , Expose fs2
  , oeffs ~ ((oeffs1 :\\ effs2) `Union` oeffs2)
  , Append (oeffs1 :\\ effs2) effs2
  , Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (oeffs1 :\\ effs2) oeffs
  , fam (Effs (oeffs1 :\\ effs2)) )
  => Handler effs1 oeffs1 fs1 fam
  -> Handler effs2 oeffs2 fs2 fam
  -> Handler effs1 ((oeffs1 :\\ effs2) `Union` oeffs2) (fs2 :++ fs1) fam
pipe (Handler h1) (Handler h2) = Handler (pipe' h1 h2)

pipe' :: forall effs1 effs2 oeffs1 oeffs2 t1 t2 fs1 fs2 oeffs fam .
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
  , Injects (oeffs1 :\\ effs2) oeffs 
  , fam (Effs (oeffs1 :\\ effs2)) )
  => Handler' effs1 oeffs1 t1 fs1 fam
  -> Handler' effs2 oeffs2 t2 fs2 fam
  -> Handler' effs1 ((oeffs1 :\\ effs2) `Union` oeffs2) (HCompose t1 t2) (fs2 :++ fs1) fam
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
    :: forall m sig . (Monad m , fam sig, HFunctor sig)
    => (forall x. sig m x -> m x)
    -> forall x. sig (HCompose t1 t2 m) x -> HCompose t1 t2 m x
  mfwd alg
    = HCompose
    . mfwd1 (mfwd2 alg)
    . hmap getHCompose

pass :: forall sig effs oeffs fs fam .
  ( All Functor fs
  , Append effs (sig :\\ effs)
  , Append (oeffs :\\ sig) sig
  , Append (oeffs :\\ sig) (sig :\\ (oeffs :\\ sig))
  , Injects sig ((oeffs :\\ sig) :++ (sig :\\ (oeffs :\\ sig)))
  , Injects oeffs ((oeffs :\\ sig) :++ sig)
  , Injects (oeffs :\\ sig) ((oeffs :\\ sig) :++ (sig :\\ (oeffs :\\ sig)))
  , Injects (sig :\\ effs) sig 
  , fam (Effs (oeffs :\\ sig))
  , fam (Effs sig) )
  => Handler effs oeffs fs fam
  -> Handler (effs `Union` sig) ((oeffs :\\ sig) `Union` sig) fs fam
pass h = fuse h (forward @sig)

forward :: Handler effs effs '[] fam
forward = Handler $ Handler'
  (const (\(IdentityT mx) -> fmap CNil mx))
  (\oalg -> IdentityT . oalg . hmap runIdentityT)
  (\alg  -> IdentityT . alg . hmap runIdentityT)


handle :: forall ieffs fs fam a .
  ( Recompose fs , All fam ieffs )
  => Handler ieffs '[] fs fam
  -> Prog ieffs a -> (Composes fs a)
handle (Handler h) p = handle' h p

handle' :: forall ieffs t fs fam a .
  ( Monad (t Identity)
  , Recompose fs, All fam ieffs )
  => Handler' ieffs '[] t fs fam
  -> Prog ieffs a -> Composes fs a
handle' (Handler' run malg mfwd)
  = runIdentity
  . fmap @Identity (recompose @fs @a)
  . run @Identity (absurdEffs . injs)
  . eval (malg (absurdEffs . injs))

handleWith :: forall ieffs oeffs xeffs m fs a fam .
  ( Monad m
  , Recompose fs
  , Append ieffs (xeffs :\\ ieffs)
  , Injects oeffs xeffs
  , Injects (xeffs :\\ ieffs) xeffs
  , fam (Effs xeffs) )
  => (forall x. Effs xeffs m x -> m x)
  -> Handler ieffs oeffs fs fam
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
  :: forall ieffs ieffs' oeffs oeffs' ts fs fam
  . ( Injects ieffs ieffs'
    , Injects oeffs oeffs'
    )
  => Handler ieffs' oeffs fs fam
  -> Handler ieffs oeffs' fs fam
weaken (Handler (Handler' run malg mfwd))
  = Handler (Handler' (\oalg -> run (oalg . injs)) (\oalg -> malg (oalg . injs) . injs) mfwd)

hide
  :: forall sigs effs oeffs f fam
  .  (Injects (effs :\\ sigs) effs, Injects oeffs oeffs)
  => Handler effs oeffs f fam -> Handler (effs :\\ sigs) oeffs f fam
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

-- Modular carriers
-- ----------------
--
-- So far the carriers of our library have always been a monad:
-- the algebras in a `Handler` are always of some monad `m`.
-- However, this is not always possible or desirable.
-- For example, although it is known that the (functorial)
-- composition of two applicatives is applicative, the
-- composition of two monads need not be a monad. Concretely,
-- the composition of `m` and the list monad `[]` is not a monad
-- (sometimes called `ListT` done wrong). It can be modelled
-- by `m [x]` for all x. Such a functor can nevertheless be a carrier:
data ListC m x = ListC (m [x])

-- The caveat is that we can use this carrier for nondet computations so long
-- as there are no scoped operations such as `search` or `once`.
--
-- Another example is ContT; since there only algebraic operations
-- can be forwarded.
data Carrier c f asig = Carrier
  { crun :: forall m x . Monad m => c m x -> m (f x)
  , calg :: forall m x . Monad m => Effs asig Identity (c m x) -> c m x
  , cfwd :: forall m x . Monad m => m (c m x) -> c m x
  , cgen :: forall m x . Monad m => x -> c m x
  }

newtype Carry (c :: (Type -> Type) -> Type -> Type)
              (m :: Type -> Type)
              a
  = Carry (forall x . Cont (c m x) a)
  deriving Functor

-- convert :: forall c f asig fam . Functor f
--   => Carrier c f asig -> Handler' asig '[] (Carry c) '[f] JustAlg
-- convert (Carrier cfwd calg crun cgen) = Handler' run alg fwd where
--   run :: Monad m
--       => (forall x. Effs '[] m x -> m x)
--       -> (forall x. Carry c m x -> m (Comps '[f] x))
--   run oalg (Carry mx) = fmap comps $ (crun (runCont mx cgen))
-- 
--   alg :: forall m . Monad m
--       => (forall x. Effs '[] m x -> m x)
--       -> (forall x. Effs asig (Carry c m) x -> Carry c m x)
--   alg oalg = go calg oalg where
--     go :: forall asig'
--        . (forall m x . Monad m => Effs asig' Identity (c m x) -> c m x)
--        -> (forall x. Effs '[] m x -> m x)
--        -> (forall x. Effs asig' (Carry c m) x -> Carry c m x)
--     go calg oalg (Eff (Alg x)) = Carry (cont (\k -> calg (fmap k (Eff (Alg x)))))
--     go calg oalg (Eff (Scp x)) = error "convert: operations should be algebraic!"
--     go calg oalg (Effs x)      = go (calg . Effs) oalg x
-- 
--   fwd :: ()
--   fwd = undefined
  -- fwd :: Monad m
  --     => (forall x. Effs sig m x -> m x)
  --     -> (forall x. Effs sig (Carry c m) x -> Carry c m x)
  -- fwd oalg (Eff (Alg x)) = Carry (cont (\k -> (cfwd . oalg . Eff . Alg)(fmap k x)))
  -- fwd oalg (Eff (Scp x)) = error "convert: Cannot forward scoped operations!"
  -- fwd oalg (Effs (x))    = fwd (oalg . Effs) x


