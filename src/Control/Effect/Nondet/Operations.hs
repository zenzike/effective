{-|
Module      : Control.Effect.Nondet.Operations
Description : Operations for the effects of nondeterministic computations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides effects and handlers for nondeterministic computations,
including choice and failure.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Effect.Nondet.Operations (
            emptyM, emptyP, pattern Empty, Empty (..), Empty_ (..),
    choose, chooseM, chooseP, pattern Choose, Choose (..), Choose_ (..),
    nondetOr, nondetOrM, nondetOrP, pattern NondetOr, NondetOr (..), NondetOr_ (..),
    once, onceM, onceP, pattern Once, Once (..), Once_ (..),
    cutFail, cutFailM, cutFailP, pattern CutFail, CutFail (..), CutFail_ (..),
    cutCall, cutCallM, cutCallP, pattern CutCall, CutCall (..), CutCall_ (..),
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
    emptyN, chooseN, nondetOrN, onceN, cutFailN, cutCallN,
#endif
   (<+>),
   select,
   selects,
   cut,
   skip,
   Alternative(..)
) where

import Control.Effect
import qualified Control.Applicative as Ap
import Control.Applicative (Alternative, (<|>))

-- * Operation declarations

$(makeAlg [e| empty :: 0 |])

$(makeScp [e| choose :: 2 |])

$(makeAlg [e| nondetOr :: 2 |])

$(makeScp [e| once :: 1 |])

-- | Signature for @CutFail@, which fails and cuts all following nondeterministic
-- siblings.
$(makeAlg [e| cutFail :: 0 |])

-- | The @CutCall@ effect represents a scoped computation with a cut boundary.
$(makeScp [e| cutCall :: 1 |])

-- * Derived operations

infixl 6 <+>
{-# INLINE (<+>) #-}
(<+>) :: Member NondetOr effs => Prog effs x -> Prog effs x -> Prog effs x
p <+> q = nondetOr p q

-- | Instance for 'Alternative' that uses @Empty@ and @Choose@.
instance (Member Empty effs, Member Choose effs)
  => Alternative (Prog effs) where
  {-# INLINE empty #-}
-- | Syntax for an empty alternative. This is an algebraic operation.
  empty :: Prog effs a
  empty = call Empty

  {-# INLINE (<|>) #-}
-- | Syntax for a choice of alternatives. This is a scoped operation.
  (<|>) :: Prog effs a -> Prog effs a -> Prog effs a
  xs <|> ys = choose xs ys

-- | `select` nondeterministically selects an element from a list.
-- If the list is empty, the computation fails.
select :: [a] -> a ! [Choose, Empty]
select xs = foldr ((<|>) . return) empty xs

-- | `selects` generates all permutations of a list, returning each element
-- along with the remaining elements of the list.
selects :: [a] -> (a, [a]) ! [Choose, Empty]
selects []      =  empty
selects (x:xs)  =  return (x, xs)  <|> do  (y, ys) <- selects xs
                                           return (y, x:ys)

-- | Perform a cut operation, pruning the search space.
cut :: (Members [Empty, Choose, CutFail] effs) => Prog effs ()
cut = skip <|> cutFail

-- | A no-op computation that does nothing.
skip :: Monad m => m ()
skip = return ()
