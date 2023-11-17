{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Redundant return" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Fuse foldr/fmap" #-}

module Control.Effect where

import Data.Kind ( Type, Constraint )

import Data.List.Kind ( type (:++) )
import Data.Functor.Identity
import Data.Functor.Composes
import Data.HFunctor
import Data.HFunctor.HComposes

import Control.Monad ( join, ap, liftM )
import Control.Monad.Trans.Class

import Data.SOP.Constraint ( All )

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

habsurd' :: Effs '[] f x -> a
habsurd' = error "habsurd!"

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
  injs = habsurd'

instance (Member x xys, Injects xs xys)
  => Injects (x ': xs) xys where
  injs (Eff x)  = inj x
  injs (Effs x) = injs x

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
  hinl = habsurd'

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
  hinl (Effs x) = Effs (hinl @xs @ys x) -- hinl @xs @ys _

  hinr :: Effs ys f a -> Effs ((x : xs) :++ ys) f a
  hinr = Effs . hinr @xs @ys

  houtl :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs (x ': xs) f a)
  houtl (Eff x)  = Just (Eff x)
  houtl (Effs x) = fmap Effs (houtl @xs @ys x)

  houtr :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs ys f a)
  houtr (Eff x)  = Nothing
  houtr (Effs x) = houtr @xs @ys x

---------------------------------------
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

-- injCall :: forall sub sup a . (Functor sub, Injects '[sub] sup) => Eff sub (Prog sup) (Prog sup a) -> Prog sup a
-- injCall = Call . (injs  @'[sub] @sup) . Eff

prjCall :: Member sub sup => Prog sup a -> Maybe (Eff sub (Prog sup) (Prog sup a))
prjCall (Call op) = prj op
prjCall _         = Nothing

data Handler' effs fs oeffs =
  forall ts . All MonadTrans ts => 
    Handler'
    { run'  :: forall m . Monad m 
           => (forall x . Effs oeffs m x -> m x)
           -> (forall x . HComps ts m x -> m (Comps fs x))

    , malg' :: forall m . Monad m
           => (forall x . Effs oeffs m x -> m x)
           -> (forall x . Effs effs (HComps ts m) (HComps ts m x) -> HComps ts m x)

    , mfwd' :: forall m sig . Monad m
           => (forall x . Effs sig m x -> m x)
           -> (forall x . Effs sig (HComps ts m) x -> HComps ts m x)

    , mret :: forall m x . x -> HComps ts m x
    }

foldM' :: forall m effs fs oeffs a .
  (Monad m, Recompose fs)
  => (forall a. Effs oeffs m a -> m a)
  -> Handler' effs fs oeffs
  -> Prog effs a -> m (Composes fs a)
foldM' oalg (Handler' run malg mfwd mret)
  = fmap recompose . run oalg . fold (malg @m oalg) mret


type Handler
  :: [Signature]                         -- effs  : input effects
  -> [(Type -> Type) -> (Type -> Type)]  -- t     : monad transformer
  -> [Type -> Type]                      -- f     : carrier type
  -> [Signature]                         -- oeffs : output effects
  -> Type
data Handler effs ts fs oeffs =
  (All Functor fs, All MonadTrans ts) =>
  Handler
  { run  :: forall m . Monad m 
         => (forall x . Effs oeffs m x -> m x)
         -> (forall x . HComps ts m x -> m (Comps fs x))

  , malg :: forall m . Monad m
         => (forall x . Effs oeffs m x -> m x)
         -> (forall x . Effs effs (HComps ts m) x -> HComps ts m x)

  , mfwd :: forall m sig . Monad m
         => (forall x . Effs sig m x -> m x)
         -> (forall x . Effs sig (HComps ts m) x -> HComps ts m x)
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
  -> Handler effs '[t] '[f] oeffs
handler runMonadT monadAlg monadFwd
  = Handler 
      (const (fmap comps . runMonadT . hdecomps))
      (\oalg -> hcomps . monadAlg oalg . hmap hdecomps)
      (\alg  -> hcomps . monadFwd alg . hmap hdecomps)

interp
  :: (forall m . Monad m
     => (forall x . Effs oeffs m x -> m x)
     -> (forall x . Effs effs m x -> m x))
  -> Handler effs '[] '[] oeffs
interp alg
  = Handler
      (const (\(HNil x) -> fmap CNil x))
      (\oalg -> HNil . alg oalg . hmap (\(HNil x) -> x))
      (\alg  -> HNil . alg . hmap (\(HNil x) -> x))

reinterp :: forall effs oeffs 
  . (forall x m . Effs effs m x -> Prog oeffs x)
  -> Handler effs '[] '[] oeffs
reinterp malg = interp alg where
  alg :: forall m . (Monad m)
    => (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs effs m x -> m x)
  alg oalg eff = eval oalg (malg eff)


type Fuse :: 
  [Signature] -> [Signature] -> [Signature] ->
  [Signature] -> [Signature] ->
  [(Type -> Type) -> (Type -> Type)] ->
  [(Type -> Type) -> (Type -> Type)] ->
  [Type -> Type] ->
  [Type -> Type] -> Constraint
class Fuse eff12 oeff1 oeff2 eff1 eff2 ts1 ts2 fs1 fs2 where
  fuse 
    :: ( Append oeff1 eff12, Append oeff1 oeff2, Append eff1 eff2
       , Injects eff12 eff2
       , All Functor (fs2 :++ fs1)
       , All MonadTrans (ts1 :++ ts2)
       , HExpose ts1
       , Expose fs2
       )
    => Handler eff1 ts1 fs1 (oeff1 :++ eff12)
    -> Handler eff2 ts2 fs2 oeff2
    -> Handler (eff1 :++ eff2) (ts1 :++ ts2) (fs2 :++ fs1) (oeff1 :++ oeff2)

-- If this were `Monad (HComposes ts2 m)` it would be illegal since
-- type families cannot appear as instance heads. We get around this by using `HComps` instead.
instance (forall m . Monad m => Monad (HComps ts2 m)) 
  => Fuse eff12 oeff1 oeff2 eff1 eff2 '[] ts2 fs1 fs2 where
  fuse
    :: (forall (m :: Type -> Type). Monad m => Monad (HComps ts2 m),
      Append oeff1 eff12, Append oeff1 oeff2, Append eff1 eff2,
      Injects eff12 eff2, All Functor (fs2 :++ fs1),
      All MonadTrans ('[] :++ ts2), HExpose '[], Expose fs2)
    => Handler eff1 '[] fs1 (oeff1 :++ eff12) -> Handler eff2 ts2 fs2 oeff2
    -> Handler (eff1 :++ eff2) ('[] :++ ts2) (fs2 :++ fs1) (oeff1 :++ oeff2)
  fuse (Handler run1 malg1 mfwd1) (Handler run2 malg2 mfwd2) =
    Handler run malg mfwd where
      run  :: forall m . Monad m
        => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
        -> (forall x . HComps ('[] :++ ts2) m x -> m (Comps (fs2 :++ fs1) x))
      run oalg
        = fmap unexpose
        . run2 (oalg . hinr @oeff1 @oeff2)
        . run1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                      (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2))
        . hexpose

      malg :: forall m sig . Monad m
        => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
        -> (forall x . Effs (eff1 :++ eff2) (HComps ('[] :++ ts2) m) x -> HComps ('[] :++ ts2) m x)
      malg oalg
        = hunexpose @'[]
        . heither @eff1 @eff2
            ( malg1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                           (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2)))
            ( mfwd1 (malg2 (oalg . hinr @oeff1 @oeff2)))
        . hmap (hexpose @'[])

      mfwd
        :: forall m sig . Monad m
        => (forall x. Effs sig m x -> m x)
        -> forall x. Effs sig (HComps ts2 m) x -> HComps ts2 m x
      mfwd alg
        = hunexpose @'[]
        . mfwd1 (mfwd2 alg)
        . hmap (hexpose @'[])

instance (forall m . Monad m => Monad (HComps ts2 m)) => Fuse eff12 oeff1 oeff2 eff1 eff2 (t1 ': ts1) ts2 fs1 fs2 where
  fuse :: (forall (m :: Type -> Type). Monad m => Monad (HComps ts2 m),
    Append oeff1 eff12, Append oeff1 oeff2, Append eff1 eff2,
    Injects eff12 eff2, All Functor (fs2 :++ fs1),
    All MonadTrans ((t1 : ts1) :++ ts2), HExpose (t1 : ts1),
    Expose fs2) => Handler eff1 (t1 : ts1) fs1 (oeff1 :++ eff12)
      -> Handler eff2 ts2 fs2 oeff2
      -> Handler (eff1 :++ eff2) ((t1 : ts1) :++ ts2) (fs2 :++ fs1) (oeff1 :++ oeff2)
  fuse (Handler run1 malg1 mfwd1) (Handler run2 malg2 mfwd2) =
    Handler run malg mfwd where
    run  :: forall m . Monad m
      => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
      -> (forall x . HComps ((t1 ': ts1) :++ ts2) m x -> m (Comps (fs2 :++ fs1) x))
    run oalg
      = fmap unexpose
      . run2 (oalg . hinr @oeff1 @oeff2)
      . run1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                    (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2))
      . hexpose

    malg :: forall m sig . Monad m
      => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
      -> (forall x . Effs (eff1 :++ eff2) (HComps ((t1 ': ts1) :++ ts2) m) x -> HComps ((t1 ': ts1) :++ ts2) m x)
    malg oalg
      = hunexpose @(t1 ': ts1)
      . heither @eff1 @eff2
          ( malg1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                         (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2)))
          ( mfwd1 (malg2 (oalg . hinr @oeff1 @oeff2)))
      . hmap (hexpose @(t1 ': ts1))

    mfwd
      :: forall m sig . Monad m
      => (forall x. Effs sig m x -> m x)
      -> forall x. Effs sig (HComps ((t1 ': ts1) :++ ts2) m) x -> HComps ((t1 ': ts1) :++ ts2) m x
    mfwd alg
      = hunexpose @(t1 ': ts1)
      . mfwd1 (mfwd2 alg)
      . hmap (hexpose @(t1 ': ts1))

(<&>)
  :: forall eff1 eff2 ts1 ts2 fs1 fs2
  .  (Fuse '[] '[] '[] eff1 eff2 ts1 ts2 fs1 fs2
     , Append eff1 eff2
     , All Functor (fs2 :++ fs1)
     , All MonadTrans (ts1 :++ ts2)
     , HExpose ts1
     , Expose fs2
     )
  => Handler eff1 ts1 fs1 '[]
  -> Handler eff2 ts2 fs2 '[]
  -> Handler (eff1 :++ eff2) (ts1 :++ ts2) (fs2 :++ fs1) '[]
(<&>) = fuse @'[] @'[] @'[] @eff1 @eff2 @ts1 @ts2 @fs1 @fs2

type Pipe :: 
  [Signature] -> [Signature] -> [Signature] ->
  [Signature] -> [Signature] ->
  [(Type -> Type) -> (Type -> Type)] ->
  [(Type -> Type) -> (Type -> Type)] ->
  [Type -> Type] ->
  [Type -> Type] -> Constraint
class Pipe eff12 oeff1 oeff2 eff1 eff2 ts1 ts2 fs1 fs2 where
  pipe 
    :: ( Append oeff1 eff12, Append oeff1 oeff2, Append eff1 eff2
       , Injects eff12 eff2
       , All Functor (fs2 :++ fs1)
       , All MonadTrans (ts1 :++ ts2)
       , HExpose ts1
       , Expose fs2
       )
    => Handler eff1 ts1 fs1 (oeff1 :++ eff12)
    -> Handler eff2 ts2 fs2 oeff2
    -> Handler eff1 (ts1 :++ ts2) (fs2 :++ fs1) (oeff1 :++ oeff2)

instance (forall m . Monad m => Monad (HComps ts2 m)) => Pipe eff12 oeff1 oeff2 eff1 eff2 '[] ts2 fs1 fs2 where
  pipe
    :: (forall (m :: Type -> Type). Monad m => Monad (HComps ts2 m),
      Append oeff1 eff12, Append oeff1 oeff2, Append eff1 eff2,
      Injects eff12 eff2, All Functor (fs2 :++ fs1),
      All MonadTrans ('[] :++ ts2), HExpose '[], Expose fs2)
    => Handler eff1 '[] fs1 (oeff1 :++ eff12) -> Handler eff2 ts2 fs2 oeff2
    -> Handler eff1 ('[] :++ ts2) (fs2 :++ fs1) (oeff1 :++ oeff2)
  pipe (Handler run1 malg1 mfwd1) (Handler run2 malg2 mfwd2) =
    Handler run malg mfwd where
      run  :: forall m . Monad m
        => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
        -> (forall x . HComps ('[] :++ ts2) m x -> m (Comps (fs2 :++ fs1) x))
      run oalg
        = fmap unexpose
        . run2 (oalg . hinr @oeff1 @oeff2)
        . run1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                      (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2))
        . hexpose

      malg :: forall m sig . Monad m
        => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
        -> (forall x . Effs (eff1) (HComps ('[] :++ ts2) m) x -> HComps ('[] :++ ts2) m x)
      malg oalg
        = hunexpose @'[]
        . (malg1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                        (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2)))
        . hmap (hexpose @'[])

      mfwd
        :: forall m sig . Monad m
        => (forall x. Effs sig m x -> m x)
        -> forall x. Effs sig (HComps ts2 m) x -> HComps ts2 m x
      mfwd alg
        = hunexpose @'[]
        . mfwd1 (mfwd2 alg)
        . hmap (hexpose @'[])

instance (forall m . Monad m => Monad (HComps ts2 m)) => Pipe eff12 oeff1 oeff2 eff1 eff2 (t1 ': ts1) ts2 fs1 fs2 where
  pipe :: (forall (m :: Type -> Type). Monad m => Monad (HComps ts2 m),
    Append oeff1 eff12, Append oeff1 oeff2, Append eff1 eff2,
    Injects eff12 eff2, All Functor (fs2 :++ fs1),
    All MonadTrans ((t1 : ts1) :++ ts2), HExpose (t1 : ts1),
    Expose fs2) => Handler eff1 (t1 : ts1) fs1 (oeff1 :++ eff12)
      -> Handler eff2 ts2 fs2 oeff2
      -> Handler eff1 ((t1 : ts1) :++ ts2) (fs2 :++ fs1) (oeff1 :++ oeff2)
  pipe (Handler run1 malg1 mfwd1) (Handler run2 malg2 mfwd2) =
    Handler run malg mfwd where
    run  :: forall m . Monad m
      => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
      -> (forall x . HComps ((t1 ': ts1) :++ ts2) m x -> m (Comps (fs2 :++ fs1) x))
    run oalg
      = fmap unexpose
      . run2 (oalg . hinr @oeff1 @oeff2)
      . run1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                    (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2))
      . hexpose

    malg :: forall m sig . Monad m
      => (forall x . Effs (oeff1 :++ oeff2) m x -> m x)
      -> (forall x . Effs eff1 (HComps ((t1 ': ts1) :++ ts2) m) x -> HComps ((t1 ': ts1) :++ ts2) m x)
    malg oalg
      = hunexpose @(t1 ': ts1)
      . (malg1 (heither @oeff1 @eff12 (mfwd2 (oalg . hinl @oeff1 @oeff2))
                                      (malg2 (oalg . hinr @oeff1 @oeff2) . injs @eff12 @eff2)))
      . hmap (hexpose @(t1 ': ts1))

    mfwd
      :: forall m sig . Monad m
      => (forall x. Effs sig m x -> m x)
      -> forall x. Effs sig (HComps ((t1 ': ts1) :++ ts2) m) x -> HComps ((t1 ': ts1) :++ ts2) m x
    mfwd alg
      = hunexpose @(t1 ': ts1)
      . mfwd1 (mfwd2 alg)
      . hmap (hexpose @(t1 ': ts1))

handleM :: forall m effs ts fs oeffs a .
  (Monad m, Monad (HComps ts m), Recompose fs)
  => (forall a. Effs oeffs m a -> m a)
  -> Handler effs ts fs oeffs
  -> Prog effs a -> m (Composes fs a)
handleM oalg (Handler run malg mfwd)
  = fmap recompose . run @m oalg . eval (malg @m oalg)

handleM' 
  :: forall eff eff' fs ts m a 
  .  (ts ~ ts :++ '[], Monad m, Append eff eff', All Functor fs
     , All MonadTrans ts, Recompose fs
     , Monad (HComps ts m)
     , Fuse '[] '[] eff' eff eff' ts '[] fs '[], HExpose ts)
  => (forall a . Effs eff' m a -> m a)
  -> Handler eff ts fs '[]
  -> Prog (eff :++ eff') a -> m (Composes fs a)
handleM' alg h = handleM alg (weaken' h)

weakenAlg
  :: forall eff eff' m x . (Injects eff (eff :++ eff'))
  => (Effs (eff :++ eff') m x -> m x)
  -> (Effs eff m x -> m x)
weakenAlg alg = alg . injs




handle :: (Monad (HComps ts Identity), Recompose fs)  =>
  Handler effs ts fs '[] -> Prog effs a -> Composes fs a
handle h
  = runIdentity . handleM habsurd' h

-- handleIO :: (Monad (HComps ts Identity), Recompose fs)  =>
--   Handler effs ts (IO ': fs) '[] -> Prog effs a -> Composes (IO ': fs) a
-- handleIO (Handler run malg mfwd)
--   = recompose . runIdentity . run @Identity habsurd' . eval (malg @Identity habsurd')

handle'
  :: (Monad (HComps ts (Prog oeffs)), Recompose fs)
  => Handler effs ts fs oeffs -> Prog effs a -> Prog oeffs (Composes fs a)
handle' (Handler run malg mfwd)
  = fmap recompose . run (Call . fmap return) . eval (malg (Call . fmap return))

handleRun
  :: (Monad (HComps ts (Prog oeffs)), Recompose fs)
  => (forall x . Effs oeffs (Prog oeffs) x -> Prog oeffs x) 
  -> Handler effs ts fs oeffs -> Prog effs a -> Prog oeffs (Composes fs a)
handleRun final (Handler run malg mfwd)
  = fmap recompose . run final . eval (malg final)

-- The parameters sig and sig' should always be instantiated manually. Good luck.
handleOne
  :: forall sig sig' eff oeffs ts fs a m
  . ( Injects oeffs sig', Injects sig sig', Append eff sig
  , Monad (HComps ts (Prog sig')), Recompose fs)
  => Handler eff ts fs oeffs -> Prog (eff :++ sig) a -> Prog sig' (Composes fs a)
handleOne (Handler run malg mfwd)
  = fmap recompose
  . run (Call . injs . fmap return)
  . eval (heither @eff @sig (malg @(Prog sig') (Call . injs . fmap return))
                            (mfwd @(Prog sig') (Call . injs . fmap return)))

weaken'
  :: forall ts fs eff eff' 
  . ( ts :++ '[] ~ ts, Append eff eff', All Functor fs, All MonadTrans ts
    , Fuse '[] '[] eff' eff eff' ts '[] fs '[]
    , HExpose ts
    )
  => Handler eff ts fs '[] -- TODO: replace '[] with oeff, using the new machinery
  -> Handler (eff :++ eff') ts fs eff'
weaken' h = fuse @'[] @'[] @eff' @eff @eff' @ts @'[] @fs @'[] h (trivial @eff')

weaken
  :: forall ts fs eff eff' oeff oeff'
  . ( ts :++ '[] ~ ts, Append eff eff', All Functor fs, All MonadTrans ts
    , Append oeff oeff'
    , Injects oeff (oeff :++ oeff')
    , Injects eff (eff :++ eff')
    )
  => Handler (eff :++ eff') ts fs oeff
  -> Handler eff ts fs (oeff :++ oeff')
weaken (Handler run malg mfwd)
  = Handler (\oalg -> run  (oalg . injs)) 
            (\oalg -> malg (oalg . injs) . injs) 
            mfwd

(\/) 
  :: forall effs1 effs2 ts fs oeffs 
  . (Append effs1 effs2)
  => Handler effs1 ts fs oeffs
  -> Handler effs2 ts fs oeffs
  -> Handler (effs1 :++ effs2) ts fs oeffs
Handler run1 malg1 mfwd1 \/ Handler run2 malg2 mfwd2
  = Handler run1 (\oalg -> heither (malg1 oalg) (malg2 oalg)) mfwd1 where
 
trivial :: Handler eff '[] '[] eff
trivial = interp id
