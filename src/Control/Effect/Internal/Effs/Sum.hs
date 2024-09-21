{-|
Module      : Control.Effect.Internal.Effs
Description : The union type for effect operations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Internal.Effs.Sum
  ( module Control.Effect.Internal.Effs.Sum.Type
  , module Control.Effect.Internal.Effs.Sum
  )
  where

import Control.Effect.Internal.Effs.Sum.Type
import Data.HFunctor
import Data.List.Kind

import GHC.TypeLits
import GHC.Exts
import Unsafe.Coerce


-- | Constructs an operation in the union @Effs effs f a@ from a single
-- operation @eff f a@, when @eff@ is in @effs@.
{-# INLINE inj #-}
inj :: forall sig sigs f a . Member sig sigs => sig f a -> Effs sigs f a
inj = inj' (proxy# @(PElemIndex sig sigs))

-- | Attempts to project an operation of type @eff f a@ from a the union @Effs effs f a@,
-- when @eff@ is in @effs@.
{-# INLINE prj #-}
prj :: forall sig sigs m a . Member sig sigs => Effs sigs m a -> Maybe (sig m a)
prj = prj' (proxy# @(PElemIndex sig sigs))

-- | @alg1 # alg2@ joins together algebras @alg1@ and @alg2@.
{-# INLINE (#) #-}
(#) :: forall eff1 eff2 m .
  (Monad m, Append eff1 eff2)
  => (Algebra eff1 m)
  -> (Algebra eff2 m)
  -> (Algebra (eff1 :++ eff2) m)
falg # galg = heither @eff1 @eff2 (falg) (galg)


type  Append :: [Effect] -> [Effect] -> Constraint
class Append xs ys where
  -- | Creates an alebra that can work with either signatures in @xeffs@
  -- or @yeffs@ by using the provided algebras as appropriate.
  heither :: (Effs xs h a -> b) -> (Effs ys h a -> b) -> (Effs (xs :++ ys) h a -> b)

  -- | Weakens an an operation of type @Effs xeffs f a@ to one of type @Effs (xeffs :++ yeffs) f a@.
  hinl :: Effs xs f a -> Effs (xs :++ ys) f a

  -- | Weakens an an operation of type @Effs yeffs f a@ to one of type @Effs (xeffs :++ yeffs) f a@.
  hinr :: Effs ys f a -> Effs (xs :++ ys) f a

  -- | Attempts to project a value of type @Effs xeffs f a@ from a union of type @Effs (xeffs :++ yeffs) f a@.
  houtl :: Effs (xs :++ ys) f a -> Maybe (Effs xs f a)

  -- | Attempts to project a value of type @Effs yeffs f a@ from a union of type @Effs (xeffs :++ yeffs) f a@.
  houtr :: Effs (xs :++ ys) f a -> Maybe (Effs ys f a)

instance Append '[] ys where
  {-# INLINE heither #-}
  heither :: (Effs '[] f a -> b) -> (Effs ys f a -> b) -> (Effs ('[] :++ ys) f a -> b)
  heither xalg yalg = yalg

  {-# INLINE hinl #-}
  hinl :: Effs '[] f a -> Effs ys f a
  hinl = undefined -- absurdEffs

  {-# INLINE hinr #-}
  hinr :: Effs ys f a -> Effs ys f a
  hinr = id

  {-# INLINE houtl #-}
  houtl :: Effs ys f a -> Maybe (Effs '[] f a)
  houtl = const Nothing

  {-# INLINE houtr #-}
  houtr :: Effs ys f a -> Maybe (Effs ys f a)
  houtr = Just

instance Append xs ys => Append (x ': xs) ys where
  {-# INLINE heither #-}
  heither :: (Effs (x : xs) f a -> b) -> (Effs ys f a -> b) -> Effs ((x : xs) :++ ys) f a -> b
  heither xalg yalg (Eff x)  = xalg (Eff x)
  heither xalg yalg (Effs x) = heither (xalg . Effs) yalg x

  {-# INLINE hinl #-}
  hinl :: Effs (x : xs) f a -> Effs ((x : xs) :++ ys) f a
  hinl (Eff x)  = Eff x
  hinl (Effs x) = Effs (hinl @xs @ys x)

  {-# INLINE hinr #-}
  hinr :: Effs ys f a -> Effs ((x : xs) :++ ys) f a
  hinr = Effs . hinr @xs @ys

  {-# INLINE houtl #-}
  houtl :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs (x ': xs) f a)
  houtl (Eff x)  = Just (Eff x)
  houtl (Effs x) = fmap Effs (houtl @xs @ys x)

  {-# INLINE houtr #-}
  houtr :: Effs ((x ': xs) :++ ys) f a -> Maybe (Effs ys f a)
  houtr (Eff x)  = Nothing
  houtr (Effs x) = houtr @xs @ys x




-- | Weakens an algera that works on @xyeffs@ to work on @xeffs@ when
-- every effect in @xeffs@ is in @xyeffs@.
{-# INLINE weakenAlg #-}
weakenAlg
  :: forall xeffs xyeffs m x . (Injects xeffs xyeffs)
  => (Effs xyeffs m x -> m x)
  -> (Effs xeffs  m x -> m x)
weakenAlg alg = alg . injs

-- | Constructs an algebra for the union containing @xeffs `Union` yeffs@
-- by using an algebra for the union @xeffs@ and aonther for the union @yeffs@.
{-# INLINE hunion #-}
hunion :: forall xeffs yeffs f a b
  .  ( Append xeffs (yeffs :\\ xeffs), Injects (yeffs :\\ xeffs) yeffs )
  => (Effs xeffs f a -> b) -> (Effs yeffs f a -> b)
  -> (Effs (xeffs `Union` yeffs) f a -> b)
hunion xalg yalg = heither @xeffs @(yeffs :\\ xeffs) xalg (yalg . injs)

-- Injects xs ys means that all of xs is in xys
-- Some other effects may be in xys, so xs <= ys
type  Injects :: [Effect] -> [Effect] -> Constraint
class Injects xs xys where
  injs :: Effs xs f a -> Effs xys f a

instance Injects '[] xys where
  {-# INLINE injs #-}
  injs :: Effs '[] f a -> Effs xys f a
  injs = absurdEffs

instance (Member x xys, Injects xs xys)
  => Injects (x ': xs) xys where
  {-# INLINE injs #-}
  injs (Eff x)  = inj x
  injs (Effs x) = injs x

class (HFunctor sig, HFunctor (Effs sigs)) => Member' sig sigs (n :: Peano) where
  inj' :: Proxy# n -> sig f a -> Effs sigs f a
  prj' :: Proxy# n -> Effs sigs f a -> Maybe (sig f a)


instance (HFunctor (Effs sigs), HFunctor sig, (sigs' ~ (sig ': sigs))) => Member' sig sigs' Zero where
  {-# INLINE inj' #-}
  inj' :: (HFunctor sig, sigs' ~ (sig : sigs)) => Proxy# Zero -> sig f a -> Effs sigs' f a
  inj' _ x = Eff x

  {-# INLINE prj' #-}
  prj' :: (HFunctor sig, sigs' ~ (sig : sigs)) => Proxy# Zero -> Effs sigs' f a -> Maybe (sig f a)
  prj' _ (Eff x) = Just x
  prj' _ _       = Nothing

instance (sigs' ~ (sig' ': sigs), HFunctor sig, HFunctor sig', Member' sig sigs n) => Member' sig sigs' (Succ n) where
  {-# INLINE inj' #-}
  inj' _ x = Effs . inj' (proxy# @n) $ x

  {-# INLINE prj' #-}
  prj' _ (Eff _)  = Nothing
  prj' _ (Effs x) = prj' (proxy# @n) x

-- | @Member eff effs@ holds when @eff@ is contained in @effs@.
type Member :: Effect -> [Effect] -> Constraint
type Member sig sigs = Member' sig sigs (PElemIndex sig sigs)

-- | @Member effs effs'@ holds when every @eff@ which is a 'Member' of in @effs@
-- is also a 'Member' of @effs'@.
type family Members (xeffs :: [Effect]) (xyeffs :: [Effect]) :: Constraint where
  Members '[] xyeffs       = ()
  Members (xeff ': xeffs) xyeffs = (Member xeff xyeffs, Members xeffs xyeffs)

-- | @`ElemIndex x xs@ finds the index of an element @x@ in the type
-- level list @xs@. Indexing starts at @0@ at the head of the list.
type family PElemIndex (x :: a) (xs :: [a]) :: Peano where
  PElemIndex x (x ': xs) = Zero
  PElemIndex x (_ ': xs) = Succ (PElemIndex x xs)

data Peano where
  Zero :: Peano
  Succ :: Peano -> Peano




