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
import Data.HFunctor
import Data.HFunctor.HCompose
import qualified Control.Monad.Graded as Graded
import Control.Monad ( join, ap, liftM )


type Effect = (Type -> Type) -> (Type -> Type)

-- type Eff :: Signature -> Effect
-- data Eff sig f x
--   = Alg (sig x)
--   | Scp (sig (f x))
--   deriving Functor
-- 
-- instance Functor sig => HFunctor (Eff sig) where
--   hmap h (Alg x) = Alg x
--   hmap h (Scp x) = Scp (fmap h x)

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


instance Graded.GradedMonad Prog where
  type Unit Prog = '[] :: [Effect]
  type Plus Prog effs effs' = Union effs effs'
  type Inv Prog effs effs' =
    ( Injects effs (Union effs effs')
    , Injects effs' (Union effs effs'))

  return = Return
  (>>=) :: forall (i :: [Effect]) (j :: [Effect]) a b.
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

injCall :: Member sub sup => sub (Prog sup) (Prog sup a) -> Prog sup a
injCall = Call . inj

prjCall :: Member sub sup => Prog sup a -> Maybe (sub (Prog sup) (Prog sup a))
prjCall (Call op) = prj op
prjCall _         = Nothing

progAlg :: Effs sig (Prog sig) a -> Prog sig a
progAlg = Call . fmap return
