{-|
Module      : Control.Effect.Internal.Algebra
Description : The data structure for storing effect operations.
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module defines the type @Algebra effs m@ of @effs@-algebras on a monad @m@.
In programming terms, an \'algebra\' is exactly an implementation of the effects
@effs@ on the notion of computation @m@. This file is logically the first file
of this library. Everything else (programs, algebra transformers, handlers, ...) is
built on top of algebras.
-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Control.Effect.Internal.Algebra (
  -- * Basic Definitions
    Effect
  , module Data.Sequence.Class
  , Algebra
  , Algebra_
  , AlgebraArray
  , Case
  , Case_

  -- * Basic interface of algebras
  , unsafeAlgebra
  , algebraFromCase
  , emptyAlg
  , tailAlg
  , viewAlg
  , toAlgebraArray
  , pattern (:#)
  , pattern (:#.)

  -- * Basic interface of cases
  , emptyCase
  , consCase
  , tailCase
  , headCase
  , viewCase
  , pattern (:%)
  , pattern (:%.)

  -- * Membership of an effect in an effect set
  , Member(..)
  , Members(..)
  , Members_(..)
  , KnownEffs(..)
  , SEffs(..)
  , dispatch
  , dispatchCases
  , dispatchC
  , singAlgIso
  , singAlg
  , callM
  , callMC
  , unsafeCallM
  , callJM
  , callKM

  -- * Appending/union algebras
  , unionAlg
  , appendCases
  , appendAlg
  , splitCase
  , splitAlg
  , (#)

  -- * Staged algebras
  , CodeQ
  , NatTrans(..)
  , type (-.>)
  , AlgebraC(..)
  , CaseC(..)
  , (#$)
  , emptyAlgC
  , emptyCaseC
  , appendAlgC
  , pattern (:#.$)
  , unionAlgC
  , weakenAlgC
  , splitAlgC
  , genAlgebra
  )
  where

import Data.List.Kind
import Data.Kind (Type, Constraint)
import Data.Sequence.Class
import qualified Data.Sequence as FT
import qualified Data.Primitive.SmallArray as Arr
import Data.Iso

import GHC.Base (Any)
import Unsafe.Coerce (unsafeCoerce)
import Language.Haskell.TH hiding (Type)

-- | The type of higher-order effects.
type Effect = (Type -> Type) -> (Type -> Type)

-- | An algebra for the effects @effs@ with carrier being the functor @f@.
-- Informally,
-- @
-- Algebra_ s [eff1, ..., eff_n] f = forall x. (eff1 f x -> f x, ..., eff_n f x -> f x)
-- @
-- The parameter @s@ is a data structure (satisfying the constraint `Sequence`) for
-- better internal representation of the components of the algebra.
newtype Algebra_
  (s :: Type -> Type)
  (effs :: [Effect])
  (f :: Type -> Type)
  = Algebra { unAlgebra :: forall x. Case_ s effs f x (f x) }

-- | The default data structure for storing algebras is finger trees.
type Algebra effs f = Algebra_ FT.Seq effs f

-- | The array-based representation is useful for fast access after we
-- construct the algebra.
type AlgebraArray effs f = Algebra_ Arr.SmallArray effs f

-- | The idea of the type is
-- @
-- Case_ s [eff1, ..., eff_n] f x y = (eff1 f x -> y, ..., eff_n f x -> y)
-- @
-- But internally the list is stored using the data structure @s@ (and the `Any` type)
-- for better time complexity.
newtype Case_
  (s :: Type -> Type)
  (effs :: [Effect])
  (f :: Type -> Type)
  (x :: Type)
  (y :: Type)
  = Case { unCase :: s Any }

type Case effs f x y = Case_ FT.Seq effs f x y

-- * Simple functions manipulating cases and algebras.
--------------------------------------------------------------------------------

-- | Unsafely construct an algebra from its components represented as the `Any` type.
{-# INLINE unsafeAlgebra #-}
unsafeAlgebra :: s Any -> Algebra_ s effs m
unsafeAlgebra cs = Algebra (Case cs)

{-# INLINE algebraFromCase #-}
algebraFromCase :: (forall x. Case_ s effs f x (f x)) -> Algebra_ s effs f
algebraFromCase = Algebra

{-# INLINE emptyCase #-}
emptyCase :: Sequence s => Case_ s '[] f x y
emptyCase = Case $ nil

{-# INLINE consCase #-}
consCase :: Sequence s => (eff f x -> y) -> Case_ s effs f x y -> Case_ s (eff ': effs) f x y
consCase f (Case fs) = Case $ cons (unsafeCoerce @_ @Any f) fs

{-# INLINE tailCase #-}
tailCase :: Sequence s => Case_ s (eff:effs) f x y -> Case_ s effs f x y
tailCase (Case aas) = case view aas of Just (_, as) -> Case as

{-# INLINE headCase #-}
headCase :: Sequence s => Case_ s (eff:effs) f x y -> (eff f x -> y)
headCase (Case aas) = case view aas of Just (a, _) -> unsafeCoerce @Any @_ a

{-# INLINE emptyAlg #-}
emptyAlg :: forall f s. Sequence s => Algebra_ s '[] f
emptyAlg = Algebra $ emptyCase

{-# INLINE tailAlg #-}
tailAlg :: forall eff effs f s. Sequence s => Algebra_ s (eff ': effs) f -> Algebra_ s effs f
tailAlg (Algebra cs) = Algebra $ tailCase cs

{-# INLINE viewCase #-}
viewCase
  :: forall eff effs m x y s.
     Sequence s
  => Case_ s (eff : effs) m x y
  -> (eff m x -> y, Case_ s effs m x y)
viewCase cs = (headCase cs, tailCase cs)

{-# INLINE viewAlg #-}
viewAlg
  :: forall eff effs m s.
     Sequence s
  => Algebra_ s (eff : effs) m
  -> (forall x. eff m x -> m x, Algebra_ s effs m)
viewAlg (Algebra aas) = (headCase aas, Algebra $ tailCase aas)

{-# INLINE toAlgebraArray #-}
toAlgebraArray :: (Sequence s) => Algebra_ s effs m -> AlgebraArray effs m
toAlgebraArray (Algebra (Case s)) = Algebra (Case (seqToArray s))

-- | The @cons@-constructor for algebras. In this library, the character @#@ is associated with
-- operations on algebras.
infixr 5 :#
{-# INLINE (:#) #-}
pattern (:#) :: Sequence s => (forall x. eff m x -> m x) -> Algebra_ s effs m -> Algebra_ s (eff : effs) m
pattern a :# as <- (viewAlg -> (a,as)) where
  a :# (Algebra as) = Algebra (consCase a as)

-- | @a :#. b@ is the same as @a :# b :# emptyAlg@
infixr 5 :#.
{-# INLINE (:#.) #-}
pattern (:#.)
  :: Sequence s
  => (forall x. eff m x -> m x)
  -> (forall x. eff' m x -> m x)
  -> Algebra_ s ([eff, eff']) m
pattern a :#. b <- (viewAlg -> (a,viewAlg -> (b, _))) where
  a :#. b = a :# (b :# emptyAlg)

-- | The @cons@-constructor for cases. In this library, the character @%@ is associated with
-- operations on cases.
infixr 5 :%
{-# INLINE (:%) #-}
pattern (:%) :: Sequence s => (eff m x -> y) -> Case_ s effs m x y -> Case_ s (eff : effs) m x y
pattern a :% as <- (viewCase -> (a,as)) where
  a :% as = consCase a as

-- | @a :%. b@ is the same as @a :% b :% emptyCase@
infixr 5 :%.
{-# INLINE (:%.) #-}
pattern (:%.)
  :: Sequence s
  => (eff m x -> y)
  -> (eff' m x -> y)
  -> Case_ s [eff, eff'] m x y
pattern a :%. b <- (viewCase -> (a,viewCase -> (b, _))) where
  a :%. b = a :% (b :% emptyCase)

-- There is a type-safe way to implement the following (by doing induction on @effs@) but the
-- following gives the correct time complexity.
instance Sequence s => Functor (Case_ s effs f x) where
  {-# INLINE fmap #-}
  fmap :: (a -> b) -> Case_ s effs f x a -> Case_ s effs f x b
  fmap f (Case cs) = Case (fmap (unsafePostcomp f) cs) where
    unsafePostcomp :: forall a b. (a -> b) -> Any -> Any
    unsafePostcomp f x = unsafeCoerce @(Any -> b) @Any $ f . unsafeCoerce @Any @(Any -> a) x

-- * Membership of an effect in effect rows
--------------------------------------------------------------------------------

-- | @Member eff effs@ is the constraint that @eff@ is a member of the list @effs@.
-- This class is inductively instantiated.
class Member (eff :: Effect) (effs :: [Effect]) where
  -- | The index of @eff@ in @effs@.
  memberIndex :: Int

  -- TODO: We are relying on GHC to optimise @(1 + 1 + ... + 0)@ to a numeral
  -- @n@ statically. A more reliable way is to make the length a type-level
  -- @Nat@ and use @KnownNat@, but this makes the error message slightly more
  -- complex, and in all tests the current implementation always has @1 + 1 + ... + 0@
  -- folded.

{-# INLINE dispatch #-}
dispatch
  :: forall eff effs s m.
     ( Member eff effs, Sequence s )
  => Algebra_ s effs m
  -> (forall x. eff m x -> m x)
dispatch (Algebra cases) = dispatchCases cases

{-# INLINE dispatchCases #-}
dispatchCases
  :: forall eff effs s m x y.
     ( Member eff effs, Sequence s )
  => Case_ s effs m x y
  -> (eff m x -> y)
dispatchCases (Case cs) = unsafeCoerce @Any (index cs (memberIndex @eff @effs))

dispatchC :: forall eff effs f. Member eff effs => AlgebraC effs f -> CodeQ (eff f -.> f)
dispatchC algC = unsafeIndex (memberIndex @eff @effs) algC where
  unsafeIndex :: forall effs'. Int -> AlgebraC effs' f -> CodeQ (eff f -.> f)
  unsafeIndex 0 (c :#$ _)  = unsafeCoerce c
  unsafeIndex n (_ :#$ cs) = unsafeIndex (n-1) cs

instance {-# OVERLAPPING #-} Member eff (eff : effs) where
  {-# INLINE memberIndex #-}
  memberIndex = 0

instance Member eff effs => Member eff (eff' : effs) where
  {-# INLINE memberIndex #-}
  memberIndex = 1 + (memberIndex @eff @effs)

-- | An obvious isomorphism between two representations of an algebra for a single effect @eff@.
{-# INLINE singAlgIso #-}
singAlgIso
  :: forall eff m s.
     Sequence s
  => Iso  (Algebra_ s '[eff] m) (forall x. eff m x -> m x)
singAlgIso = Iso dispatch singAlg

{-# INLINE singAlg #-}
singAlg :: Sequence s => (forall x. eff m x -> m x) -> Algebra_ s '[eff] m
singAlg alg = alg :# emptyAlg

-- | A variant of `Control.Effect.call` for which the effect is on a given monad
-- rather than the `Control.Effect.Prog` monad.
{-# INLINE callM #-}
callM :: forall eff effs a m s . (Member eff effs, Sequence s)
      => Algebra_ s effs m -> eff m a -> m a
callM oalg = dispatch oalg

-- | A staged variant of `callM`.
callMC
  :: forall eff effs a m x.
     (Member eff effs)
  => AlgebraC effs m
  -> CodeQ (eff m x -> m x)
callMC oalg = [|| at $$(dispatchC oalg) ||]

-- | @unsafeCallM n oalg@ is the @n@-th component of @oalg@.
unsafeCallM
  :: forall eff effs a m s.
     Sequence s
  => Int
  -> Algebra_ s effs m
  -> eff m a
  -> m a
unsafeCallM n (Algebra (Case cs)) = unsafeCoerce @Any @(forall x. eff m x -> m x) (index cs n)

-- | A variant of @callJ@ for which the effect is on a given monad rather than the @Prog@ monad.
{-# INLINE callJM #-}
callJM
  :: forall eff effs a m s.
     ( Monad m, Member eff effs, Sequence s )
  => Algebra_ s effs m
  -> eff m (m a)
  -> m a
callJM oalg x = callM oalg x >>= id

-- | A variant of @callK@ for which the effect is on a given monad rather than the @Prog@ monad.
{-# INLINE callKM #-}
callKM
  :: forall eff effs a b m s.
     ( Monad m, Member eff effs, Sequence s )
  => Algebra_ s effs m
  -> eff m a
  -> (a -> m b)
  -> m b
callKM oalg x k = callM oalg x >>= k

-- * Weakening and concatenating algebras
--------------------------------------------------------------------------------

-- | @Members xeffs yeffs@ expresses that @xeffs@ is a subset of @yeffs@.
-- Alongside @'Members_' xeffs yeffs@, @'KnownEffs' xeffs@ is needed for
-- weakening an algebra of @yeffs@ to an algebra of @xeffs@ by 'weakenAlg'.
type Members xeffs yeffs = (Members_ xeffs yeffs, KnownEffs xeffs)

-- | @Members_ effs effs'@ holds when every @eff@ which is a 'Member' of @effs@
-- is also a 'Member' of @effs'@.
type family Members_ (xeffs :: [Effect]) (xyeffs :: [Effect]) :: Constraint where
  Members_ '[]             xyeffs = ()
  Members_ (xeff ': xeffs) xyeffs = (Member xeff xyeffs, Members_ xeffs xyeffs)

-- | Runtime representation of a list of effects.
data SEffs (effs :: [Effect]) where
  SNil :: SEffs '[]
  SCons :: forall eff effs. SEffs effs -> SEffs (eff ': effs)

-- | @KnownEffs xeffs@ holds when @xeffs@ is a canonical element of @[Effect]@; that is,
-- @xeffs@ is built from @[]@ and @:@. This allows us to do induction on @xeffs@.
class KnownEffs (xeffs :: [Effect]) where
  -- | Runtime representation of @xeffs@. By induction on @singEffs@, the other
  -- members such as @lengthEffs@ can be defined, but we still include them in
  -- this type class so that they can be statically simplified by GHC (GHC doesn't
  -- simplify recursive definitions, but it simplifies recursive type instances).
  singEffs :: SEffs xeffs

  -- | The number of effects in @xeffs@
  lengthEffs :: Int

  -- | Weakens an algebra that works on @xyeffs@ to work on @xeffs@ when
  -- every effect in @xeffs@ is in @xyeffs@.
  weakenAlg
    :: forall xyeffs s m.
       ( Members_ xeffs xyeffs, Sequence s )
    => Algebra_ s xyeffs m
    -> Algebra_ s xeffs m

instance KnownEffs '[] where
  {-# INLINE singEffs #-}
  singEffs = SNil

  {-# INLINE lengthEffs #-}
  lengthEffs = 0

  {-# INLINE weakenAlg #-}
  weakenAlg _ = emptyAlg

instance KnownEffs effs => KnownEffs (eff : effs) where
  {-# INLINE singEffs #-}
  singEffs = SCons singEffs

  {-# INLINE lengthEffs #-}
  lengthEffs = 1 + lengthEffs @effs

  {-# INLINE weakenAlg #-}
  weakenAlg xyAlg = dispatch xyAlg :# weakenAlg @effs xyAlg

-- | Constructs an algebra for the union containing @xeffs `Union` yeffs@
-- by using an algebra for the union @xeffs@ and another for the union @yeffs@.
-- If an effect is in both @xeffs@ and @yeffs@, the algebra for @xeffs@ is used.
{-# INLINE unionAlg #-}
unionAlg
  :: forall xeffs yeffs m s.
     ( Members (yeffs :\\ xeffs) yeffs, Sequence s )
  => Algebra_ s xeffs m
  -> Algebra_ s yeffs m
  -> Algebra_ s (xeffs `Union` yeffs) m
unionAlg xalg yalg = appendAlg @xeffs @(yeffs :\\ xeffs) xalg (weakenAlg yalg)

{-# INLINE appendCases #-}
appendCases
  :: Sequence s
  => Case_ s xeffs m x y
  -> Case_ s yeffs m x y
  -> Case_ s (xeffs :++ yeffs) m x y
appendCases (Case xs) (Case ys) = Case (append xs ys)

{-# INLINE appendAlg #-}
appendAlg
  :: forall xeffs yeffs m s.
     Sequence s
  => Algebra_ s xeffs m
  -> Algebra_ s yeffs m
  -> Algebra_ s (xeffs :++ yeffs) m
appendAlg (Algebra as) (Algebra bs) = Algebra $ appendCases as bs

infixr 6 #
-- | @alg1 # alg2@ joins together algebras @alg1@ and @alg2@.
{-# INLINE (#) #-}
(#)
  :: forall eff1 eff2 m s.
     Sequence s
  => Algebra_ s eff1 m
  -> Algebra_ s eff2 m
  -> Algebra_ s (eff1 :++ eff2) m
falg # galg = appendAlg falg galg


{-# INLINE splitCase #-}
splitCase
  :: forall xeffs yeffs f x y s.
     ( Sequence s, KnownEffs xeffs )
  => Case_ s (xeffs :++ yeffs) f x y
  -> (Case_ s xeffs f x y, Case_ s yeffs f x y)
splitCase (Case s) = let (l, r) = split s (lengthEffs @xeffs)
                     in (Case l, Case r)

{-# INLINE splitAlg #-}
splitAlg
  :: forall xeffs yeffs m s.
     ( Sequence s, KnownEffs xeffs )
  => Algebra_ s (xeffs :++ yeffs) m
  -> (Algebra_ s xeffs m, Algebra_ s yeffs m)
splitAlg (Algebra (Case s))
  = let (l, r) = split s (lengthEffs @xeffs)
    in (Algebra (Case l), Algebra (Case r))

-- * | Definitions related to staged algebras
---------------------------------------------

-- | In current GHC, polymorphic functions and Template Haskell don't seem to work
-- seamlessly together. Newtype wrappers seem necessary in some cases.
newtype NatTrans f g = NT { at :: forall x. f x -> g x }
type (-.>) = NatTrans

infixr 5 :#$

-- | Staged version of @effs@-algebras on @f@. We are using a GADT to represent
-- staged algebras. In the future this may be changed to efficient sequence data
-- structures for faster compilation speed.
data AlgebraC (effs :: [Effect]) (f :: Type -> Type) where
  EmptyAlgC :: AlgebraC '[] f
  (:#$) :: CodeQ (eff m -.> m) -> AlgebraC effs m -> AlgebraC (eff ': effs) m

data CaseC (effs :: [Effect]) (f :: Type -> Type) a b where
  EmptyCaseC :: CaseC '[] f a b
  (:#%) :: CodeQ (eff f a -> b) -> CaseC effs f a b -> CaseC (eff ': effs) f a b

-- | For consistency with @emptyAlg@, we define a synonym @emptyAlgC@ of @EmptyAlgC@.
emptyAlgC :: AlgebraC '[] f
emptyAlgC = EmptyAlgC

-- | For consistency with @emptyCase@, we define a synonym @emptyCaseC@ of @EmptyCaseC@.
emptyCaseC :: CaseC '[] f a b
emptyCaseC = EmptyCaseC

-- | @alg1 #$ alg2@ joins together code of algebras @alg1@ and @alg2@.
infixr 6 #$
(#$), appendAlgC :: forall eff1 eff2 m .
     AlgebraC eff1 m
  -> AlgebraC eff2 m
  -> AlgebraC (eff1 :++ eff2) m
EmptyAlgC #$ galg = galg
(a :#$ as) #$ galg = a :#$ (as #$ galg)

appendAlgC = (#$)

-- | It is useful in @a :#.$ b :#.$ c :#.$ d@ to end a sequence of staged algebras.
infixr 5 :#.$
pattern (:#.$) :: CodeQ (eff m -.> m) -> CodeQ (eff' m -.> m) -> AlgebraC ([eff, eff']) m
pattern a :#.$ b = (a :#$ (b :#$ EmptyAlgC))

-- | Staged version of `unionAlg`.
unionAlgC
  :: forall xeffs yeffs m a b.
     (Members (yeffs :\\ xeffs) yeffs)
  => AlgebraC xeffs m
  -> AlgebraC yeffs m
  -> AlgebraC (xeffs `Union` yeffs) m
unionAlgC xalg yalg = (#$) @xeffs @(yeffs :\\ xeffs) xalg (weakenAlgC yalg)

-- | Weaken a staged algebra.
weakenAlgC :: forall xs ys m. Members xs ys => AlgebraC ys m -> AlgebraC xs m
weakenAlgC = go (singEffs @xs) where
  go :: forall xs'. Members_ xs' ys => SEffs xs' -> AlgebraC ys m -> AlgebraC xs' m
  go SNil _ = EmptyAlgC
  go (SCons s) cxys = dispatchC cxys :#$ go s cxys

-- | To split a staged algebra @AlgebraC (xs :++ ys) m@ we need to perform
-- induction on @xs@, so we need @KnownEffs xs@.
splitAlgC :: forall xs ys m. KnownEffs xs => AlgebraC (xs :++ ys) m -> (AlgebraC xs m, AlgebraC ys m)
splitAlgC = go singEffs where
  go :: forall xs'. SEffs xs' -> AlgebraC (xs' :++ ys) m -> (AlgebraC xs' m, AlgebraC ys m)
  go SNil cbs = (EmptyAlgC, cbs)
  go (SCons s) (ca :#$ cabs) = let (cas, cbs) = go s cabs in ((ca :#$ cas), cbs)

-- | Generate code for an algebra from a staged algebra.
genAlgebra :: AlgebraC effs f -> CodeQ (Algebra effs f)
genAlgebra EmptyAlgC = [|| emptyAlg ||]
genAlgebra (ac :#$ acs) = [|| at $$ac :# $$(genAlgebra acs) ||]
