{-|
Module      : Data.List.Kind
Description : Type-level programming with type lists
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides various functions for working with type lists.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.List.Kind where
import Data.Kind (Constraint)

import GHC.TypeLits

-- | List concatenation.
type family (xs :: [k]) :++ (ys :: [k]) :: [k] where
  '[]       :++ ys = ys
  (x ': xs) :++ ys = x ': (xs :++ ys)

type family Head (xs :: [k]) :: k where
  Head (x ': xs) = x

type family Tail (xs :: [k]) :: [k] where
  Tail xs = xs

-- | @`Insert` x ys@ inserts a type @x@ into a type list @ys@.
type family Insert (x :: k) (ys :: [k]) :: [k] where
  Insert x '[]       = '[x]
  Insert x (x ': ys) = x ': ys
  Insert x (y ': ys) = y ': Insert x ys

-- | @`Delete` x ys@ deletes a type @x@ from a type list @ys@.
type family Delete (x :: k) (ys :: [k]) :: [k] where
  Delete x '[]       = '[]
  Delete x (x ': ys) = ys
  Delete x (y ': ys) = y ': Delete x ys

-- | @`Reverse` xs@ reverses a type list @xs@, this uses `Reverse'` for
-- an O(n) implementation.
type family Reverse (xs :: [k]) :: [k] where
  Reverse xs = Reverse' xs '[]

-- | @`Reverse'` xs sx@ reverses the list @xs@ an appends it to the
-- front of @sx@.
type family Reverse' (xs :: [k]) (sx :: [k]) :: [k] where
  Reverse' '[]       sx = sx
  Reverse' (x ': xs) sx = Reverse' xs (x ': sx)

-- | @xs `:\\` ys@ removes all types in @ys@ from @xs@, leaving
-- the order of untouched types the same.
type family ((xs :: [k]) :\\ (ys :: [k]))  :: [k] where
  xs :\\ '[]       = xs
  xs :\\ (y ': ys) = (Delete y xs) :\\ ys

-- |@`Union` xs ys@ takes the union of the types @xs@ with @ys@
type Union xs ys = xs :++ (ys :\\ xs)

-- |@`Inter` xs ys@ takes the intersection of the types @xs@ with @ys@
type Inter xs ys = xs :\\ (xs :\\ ys)

-- | Given a constraint @c@ and a list of values @xs@, @`All` c xs@ builds a
-- constraint that witnesses that each element @x@ in @xs@ satisfies @c@.
type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c '[]       = ()
  All c (x ': xs) = (c x, All c xs)

-- | @`ElemIndex x xs@ finds the index of an element @x@ in the type
-- level list @xs@. Indexing starts at @0@ at the head of the list.
type family ElemIndex (x :: a) (xs :: [a]) :: Nat where
  ElemIndex x (x ': xs) = 0
  ElemIndex x (_ ': xs) = 1 + (ElemIndex x xs)

-- | Given @xs@ which is a sublist of @ys@ the type family
-- @`ElemIndexes` xs ys@ finds the index @ElemIndex x ys@ for each @x@ in @xs@,
-- and returns this as a list of indices.
type family ElemIndexes (xs :: [a]) (ys :: [a]) :: [Nat] where
  ElemIndexes '[]       ys = '[]
  ElemIndexes (x ': xs) ys = ElemIndex x ys ': ElemIndexes xs ys

-- | @`Length` xs@ returns the length of the type level list @xs@ as a @Nat@.
type family Length (xs :: [a]) :: Nat where
  Length '[]       = 0
  Length (_ ': xs) = 1 + Length xs

-- | @`Lookup` n xs@ returns the @n@th element of @xs@.
type family Lookup (n :: Nat) (xs :: [a]) :: a where
  Lookup 0 (x ': xs) = x
  Lookup n (x ': xs) = Lookup (n - 1) xs

-- | @`Foldr f k xs` peforms a type-level @foldr@ on the list of types @xs@.
type family Foldr (f :: a -> b -> b) (k :: b) (xs :: [a]) :: b where
  Foldr f k '[]       = k
  Foldr f k (x ': xs) = f x (Foldr f k xs)

-- | @`Foldr0 f k xs` returns @k@ when the list is empty, and peforms
-- @Foldr1 f xs@ otherwise.
type family Foldr0 (f :: a -> a -> a) (k :: a) (xs :: [a]) :: a where
  Foldr0 f k '[] = k
  Foldr0 f k xs  = Foldr1 f xs

-- | @`Foldr1 f xs` peforms a type-level @foldr1@ on the list of types @xs@,
-- which assumes that @xs@ is non-empty.
type family Foldr1 (f :: a -> a -> a) (xs :: [a]) :: a where
  Foldr1 f '[x]      = x
  Foldr1 f (x ': xs) = f x (Foldr1 f xs)

-- | @`Map f xs` peforms a type-level @map@ on the list of types @xs@.
type family Map (f :: a -> b) (xs :: [a]) :: [b] where
  Map f '[]       = '[]
  Map f (x ': xs) = f x ': Map f xs

-- | @`Apply fs a`@ applies a list @fs@ of type-level functions to the given @a@.
type family Apply (fs :: [k -> k]) (a :: k) where
  Apply '[] a     = a
  Apply (f:fs) a  = f (Apply fs a)

-- | For all closed type-level lists @fs1@ and @fs2@, the type @Apply fs1 (Apply fs2 a)@ 
-- and @@Apply (fs1 :++ fs2) a@ will be exactly the same, but GHC doesn't know this, so
-- whenever we need this, we will need to manually assume this as a constraint @Assoc fs1 fs2 a@,
-- which is going to be automatically discharged when @fs1@ and @fs2@ are substituted by closed lists.

class (Apply fs1 (Apply fs2 a) ~ Apply (fs1 :++ fs2) a) => Assoc fs1 fs2 a where
instance (Apply fs1 (Apply fs2 a) ~ Apply (fs1 :++ fs2) a) => Assoc fs1 fs2 a where