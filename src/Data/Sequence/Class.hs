{-|
Module      : Data.Sequence.Class
Description : An interface for sequence-like data structures
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module defines a typeclass `Sequence` for data structures that store
sequences of elements, such as lists, finger trees, and arrays. In this library,
we store the handling code of effectful operations as a sequence, but we do
not need to commit to a fixed data structure, so `Sequence` is defined.
-}
module Data.Sequence.Class where

import Data.Kind (Type)

import qualified Data.Sequence as S
import qualified Data.Primitive.SmallArray as A
import qualified Data.Array as A
import Data.Foldable

-- | @Sequence l@ expresses that @l@ is a data structure for sequences of elements.
class Functor l => Sequence (l :: Type -> Type) where
  -- | Empty sequence.
  nil :: l a

  -- | Add one element to the head of a sequence.
  cons :: a -> l a -> l a

  -- | Concatenate two sequences.
  append :: l a -> l a -> l a

  -- | Look up in the sequence.
  index :: l a -> Int -> a

  -- | Pattern match the sequence: @Nothing@ means it is empty, and @Just (a, as)@
  -- means that the sequence is @cons a as@.
  view :: l a -> Maybe (a, l a)

  -- | @fst (split l n)@ is the first @n@ elements of @l@. When @l@ doesn't have
  -- @n@ elements, @fst (split l n)@ should be equal to @l@. @snd (split l n)@
  -- should be the rest of the elements in @l@ after @fst (split l n)@.
  split :: l a -> Int -> (l a, l a)

  -- | Convert the sequence to an array.
  seqToArray :: l a -> A.SmallArray a

  -- | Convert from an array.
  seqFromArray :: A.SmallArray a -> l a

  -- | Convert the sequence to a list.
  seqToList :: l a -> [a]

  -- | Convert from a list.
  seqFromList :: [a] -> l a

-- | Lists are fast for accessing the head.
instance Sequence [] where
  {-# INLINE nil#-}
  nil = []
  {-# INLINE cons #-}
  cons = (:)
  {-# INLINE append #-}
  append = (++)
  {-# INLINE index #-}
  index = (!!)
  {-# INLINE view #-}
  view [] = Nothing
  view (a:as) = Just (a, as)
  {-# INLINE split #-}
  split xs n = (take n xs, drop n xs)
  {-# INLINE seqToArray #-}
  seqToArray = A.smallArrayFromList
  {-# INLINE seqFromArray #-}
  seqFromArray = toList
  {-# INLINE seqToList #-}
  seqToList = id
  {-# INLINE seqFromList #-}
  seqFromList = id


-- | Finger trees are reasonably fast for all operations.
instance Sequence S.Seq where
  {-# INLINE nil#-}
  nil = S.empty
  {-# INLINE cons #-}
  cons = (S.<|)
  {-# INLINE append #-}
  append = (S.><)
  {-# INLINE index #-}
  index = S.index
  {-# INLINE view #-}
  view x = case S.viewl x of
    S.EmptyL -> Nothing
    a S.:< as -> Just (a, as)
  {-# INLINE split #-}
  split l n = S.splitAt n l
  {-# INLINE seqToArray #-}
  seqToArray = A.smallArrayFromList . toList
  {-# INLINE seqFromArray #-}
  seqFromArray = S.fromList . toList
  {-# INLINE seqToList #-}
  seqToList = toList
  {-# INLINE seqFromList #-}
  seqFromList = S.fromList

-- | Arrays are very fast for indexing and destruction but very slow for construction.
instance Sequence A.SmallArray where
  {-# INLINE nil#-}
  nil = A.emptySmallArray
  {-# INLINE cons #-}
  cons a as = A.smallArrayFromList (a : toList as)
  {-# INLINE append #-}
  append as bs = A.smallArrayFromList (toList as ++ toList bs)
  {-# INLINE index #-}
  index as n = A.indexSmallArray as n
  {-# INLINE view #-}
  view as = case length as of
    0 -> Nothing
    n -> Just (A.indexSmallArray as 0, A.cloneSmallArray as 1 (n-1))
  {-# INLINE split #-}
  split l n = let size = A.sizeofSmallArray l
              in if size <= n
                   then (l, A.emptySmallArray)
                   else (A.cloneSmallArray l 0 n, A.cloneSmallArray l n (size - n))
  {-# INLINE seqToArray #-}
  seqToArray = id
  {-# INLINE seqFromArray #-}
  seqFromArray = id
  {-# INLINE seqToList #-}
  seqToList = toList
  {-# INLINE seqFromList #-}
  seqFromList = A.smallArrayFromList