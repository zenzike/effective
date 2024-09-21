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

module Control.Effect.Internal.Effs.Indexed
  ( module Control.Effect.Internal.Effs.Indexed.Type
  , module Control.Effect.Internal.Effs.Indexed
  , module Control.Effect.Internal.Effs.Indexed.Class
  )
  where

import Control.Effect.Internal.Effs.Indexed.Type
import Control.Effect.Internal.Effs.Indexed.Class
import Data.HFunctor
import Data.List.Kind

import GHC.TypeLits
import GHC.Exts
import Unsafe.Coerce

--	total alloc = 928,740,800 bytes  (excludes profiling overheads)
-- 	total time  =        0.35 secs   (348 ticks @ 1000 us, 1 processor)

-- import Control.Effect.Internal.Effs.Array
--	total time  =        0.36 secs   (359 ticks @ 1000 us, 1 processor)
--	total alloc = 1,023,990,040 bytes  (excludes profiling overheads)

-- | Matches an effect @eff@ at the head of a signature @eff ': effs@.

{-# INLINE Eff #-}
pattern Eff :: (HFunctor eff, KnownNat (1 + Length effs), KnownNat (Length effs))
  => eff f a -> Effs (eff ': effs) f a
pattern Eff op <- (openEff -> Just op) where
  Eff op = inj op

{-# INLINE Effs #-}
-- | Matches the tail @effs@ of effects of a signature @eff ': effs@.
pattern Effs :: forall eff effs f a . KnownNat (Length effs)
  => Effs effs f a -> Effs (eff ': effs) f a
pattern Effs op <- (openEffs -> Just op) where
  Effs op = coerce @(Effs effs f a) @(Effs (eff ': effs) f a) op

-- | Inspects an operation in the union @eff ': effs@ and returns the operation
-- specialied to @eff@ if possible, or a union @effs@ otherwise.
{-# INLINE open #-}
open :: forall eff effs f a . KnownNat (Length effs) => Effs (eff ': effs) f a -> Either (Effs effs f a) (eff f a)
open  eff@(Effn n (op :: peff f a))
  | n == fromInteger (natVal' (proxy#@(Length effs))) = Right (unsafeCoerce @(peff f a) @(eff f a) op)
  | otherwise                                         = Left (coerce @(Effs (eff ': effs) f a) @(Effs effs f a) eff)

-- | Inspects an operation in the union @eff ': effs@ and returns the operation
-- specialied to @eff@ if possible.
{-# INLINE openEff #-}
openEff :: forall eff effs f a . Member eff effs
  => Effs effs f a -> Maybe (eff f a)
openEff (Effn n op)
  | n == n'   = Just (unsafeCoerce @(_ f a) @(eff f a) op)
  | otherwise = Nothing
  where n' = fromInteger (natVal' (proxy#@(EffIndex eff effs)))

-- | Inspects an operation in the union @eff ': effs@ and returns
-- a union @effs@ if possible.
{-# INLINE openEffs #-}
openEffs :: forall eff effs f a . KnownNat (Length effs)
  => Effs (eff ': effs) f a -> Maybe (Effs effs f a)
openEffs effn@(Effn n op)
  | n == m    = Nothing
  | otherwise = Just (coerce @(Effs (eff ': effs) f a) @(Effs effs f a) effn)
  where m = fromInteger (natVal' (proxy#@(Length effs)))


-- | Constructs an operation in the union @Effs effs f a@ from a single
-- operation @eff f a@, when @eff@ is in @effs@.
{-# INLINE inj #-}
inj :: forall eff effs f a . (HFunctor eff, Member eff effs) => eff f a -> Effs effs f a
inj = Effn n
  where
    n = fromInteger (natVal' (proxy# @(EffIndex eff effs)))

-- | Attempts to project an operation of type @eff f a@ from a the union @Effs effs f a@,
-- when @eff@ is in @effs@.
{-# INLINE prj #-}
prj :: forall eff effs f a . (Member eff effs)
  => Effs effs f a -> Maybe (eff f a)
prj (Effn n x)
  | n == n'   = Just (unsafeCoerce @(_ f a) @(eff f a) x)
  | otherwise = Nothing
  where
    n' = fromInteger (natVal' (proxy# @(EffIndex eff effs)))

-- | @alg1 # alg2@ joins together algebras @alg1@ and @alg2@.
{-# INLINE (#) #-}
(#) :: forall eff1 eff2 m .
  (Monad m, KnownNat (Length eff2))
  => (Algebra eff1 m)
  -> (Algebra eff2 m)
  -> (Algebra (eff1 :++ eff2) m)
falg # galg = heither @eff1 @eff2 (falg) (galg)

-- | Weakens the signature of an operation in the union containing @effs@
-- to one that contains @eff ': effs@ for any @eff@.
{-# INLINE weakenEffs #-}
weakenEffs :: forall eff effs f a . Effs effs f a -> Effs (eff ': effs) f a
weakenEffs = coerce @(Effs effs f a) @(Effs (eff ': effs) f a)

instance Functor f => Functor (Effs effs f) where
  {-# INLINE fmap #-}
  fmap f (Effn n op) = Effn n (fmap f op)

instance HFunctor (Effs effs) where
  {-# INLINE hmap #-}
  hmap h (Effn n op) = Effn n (hmap h op)



-- | Weakens an an operation of type @Effs xeffs f a@ to one of type @Effs (xeffs :++ yeffs) f a@.
{-# INLINE hinl #-}
hinl :: forall xeffs yeffs f a . KnownNat (Length yeffs)
  => Effs xeffs f a -> Effs (xeffs :++ yeffs) f a
hinl (Effn n op) = Effn (m + n) op
  where
    -- m = fromInteger (fromSNat (natSing @(Length yeffs)))
    m = fromInteger (natVal' (proxy# @(Length yeffs)))

-- | Weakens an an operation of type @Effs yeffs f a@ to one of type @Effs (xeffs :++ yeffs) f a@.
{-# INLINE hinr #-}
hinr :: forall xeffs yeffs f a . Effs yeffs f a -> Effs (xeffs :++ yeffs) f a
hinr = coerce @(Effs yeffs f a) @(Effs (xeffs :++ yeffs) f a)

-- | Attempts to project a value of type @Effs xeffs f a@ from a union of type @Effs (xeffs :++ yeffs) f a@.
{-# INLINE houtl #-}
houtl :: forall xeffs yeffs f a . KnownNat (Length yeffs)
  => Effs (xeffs :++ yeffs) f a -> Maybe (Effs xeffs f a)
houtl (Effn n op)
  | n < m     = Nothing
  | otherwise = Just (Effn (n - m) op)
  where
    m = fromInteger (natVal' (proxy# @(Length yeffs)))

-- | Attempts to project a value of type @Effs yeffs f a@ from a union of type @Effs (xeffs :++ yeffs) f a@.
{-# INLINE houtr #-}
houtr :: forall xeffs yeffs f a . KnownNat (Length yeffs)
  => Effs (xeffs :++ yeffs) f a -> Maybe (Effs yeffs f a)
houtr effn@(Effn n op)
  | n < m     = Just (coerce @(Effs (xeffs :++ yeffs) f a) @(Effs yeffs f a) effn)
  | otherwise = Nothing
  where
    m = fromInteger (natVal' (proxy# @(Length yeffs)))


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
hunion :: forall xeffs yeffs f a b . Injects (yeffs :\\ xeffs) yeffs
  => (Effs xeffs f a -> b) -> (Effs yeffs f a -> b)
  -> (Effs (xeffs `Union` yeffs) f a -> b)
hunion xalg yalg = heither @xeffs @(yeffs :\\ xeffs) xalg (yalg . injs)

-- | Creates an alebra that can work with either signatures in @xeffs@
-- or @yeffs@ by using the provided algebras as appropriate.
{-# INLINE heither #-}
heither :: forall xeffs yeffs f a b . KnownNat (Length yeffs)
  => (Effs xeffs f a -> b) -> (Effs yeffs f a -> b) -> (Effs (xeffs :++ yeffs) f a -> b)
heither xalg yalg (Effn n op)
  | n < m     = yalg (Effn n op)
  | otherwise = xalg (Effn (n - m) op)
  where
    -- m = fromInteger (fromSNat (natSing @(Length yeffs)))
    m = fromInteger (natVal' (proxy#@(Length yeffs)))

type Append xs ys = (KnownNat (Length ys))