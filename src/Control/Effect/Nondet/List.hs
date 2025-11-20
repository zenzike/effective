{-|
Module      : Control.Effect.Nondet.List
Description : Effects for nondeterministic computations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides effects and handlers for nondeterministic computations,
including choice and failure.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Nondet.List
  ( Choose
  , Empty
  , nondet, nondetAT
  , nondet'
  , Once
  , Once_ (..)
  , once
  , list
  , backtrack
  , backtrack'
  , backtrackAlg
  , backtrackOnceAlg
  ) where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Alternative

import Control.Effect.Nondet.Type
import Control.Monad.Trans.List

list :: Handler [Empty, Choose] '[] '[ListT] a [a]
list = alternative runListT'

list' :: Handler [Search, Empty, Choose] '[] '[ListT] a [a]
list' = searchListAlg #: list

searchListAlg :: AlgTrans '[Search] '[] '[ListT] Monad
searchListAlg = algTrans1 $ \oalg (Scp (Search_ xs)) -> xs


nondet' :: Handler [Empty, Choose, Nondet] '[] '[ListT] a [a]
nondet' = handler' runListT' (\oalg -> nondet'Alg oalg)

{-# INLINE nondet'Alg #-}
nondet'Alg
  :: forall oeffs
  . forall m. Monad m
  => Algebra oeffs m -> Algebra [Empty, Choose, Nondet] (ListT m)
nondet'Alg oalg eff
  | (Just (Alg Empty_))          <- prj eff = empty
  | (Just (Scp (Choose_ xs ys))) <- prj eff = xs <|> ys
  | (Just (Alg (Choose_ xs ys))) <- prj eff = pure xs <|> pure ys

-- | The `nondet` handler transforms nondeterministic effects t`Empty` and t`Choose`
-- into the t`ListT` monad transformer, which collects all possible results.
{-# INLINE nondet #-}
nondet :: Handler [Empty, Nondet] '[] '[ListT] a [a]
nondet = handler' runListT' nondetAlg

{-# INLINE nondetAlg #-}
nondetAlg
  :: forall oeffs
  . forall m. Monad m
  => Algebra oeffs m -> Algebra [Empty, Nondet] (ListT m)
nondetAlg oalg eff
  | (Just (Alg Empty_))          <- prj eff = empty
  | (Just (Alg (Choose_ xs ys))) <- prj eff = pure xs <|> pure ys

{-# INLINE nondetAT #-}
-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying 'Alternative' instance for @t m@ given by a transformer @t@.
nondetAT
  :: AlgTrans '[Empty, Nondet] '[] '[ListT] Monad
nondetAT = AlgTrans nondetAlg

-- | `backtrack` is a handler that transforms nondeterministic effects
-- t`Empty`, t`Choose`, and t`Once` into the t`ListT` monad transformer,
-- supporting backtracking.
backtrack :: Handler [Empty, Choose, Nondet, Once] '[] '[ListT] a [a]
backtrack = handler' runListT' (\oalg -> alternativeAlg oalg # nondetAlg' # onceAlg')

nondetAlg' :: Monad m => Algebra '[Nondet]  (ListT m)
nondetAlg' eff | Just (Alg (Choose_ x y)) <- prj eff = pure x <|> pure y

onceAlg' :: Monad m => Algebra '[Once]  (ListT m)
onceAlg' (Once xs) = ListT $ do
  mx <- runListT xs
  case mx of Nothing       -> return Nothing
             Just (x, mxs) -> return (Just (x, empty))



-- | `backtrack'` is a handler that transforms nondeterministic effects
-- t`Empty`, t`Choose`, and t`Once` into the t`ListT` monad transformer,
-- supporting backtracking.
backtrack' :: Handler [Empty, Nondet, Once] '[] '[ListT] a [a]
backtrack' = handler' runListT' backtrackAlg

-- | `backtrackAlg` defines the semantics of backtracking for the t`Empty`,
-- t`Choose`, and t`Once` effects in the context of the t`ListT` monad transformer.
backtrackAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Empty, Nondet, Once] (ListT m) x -> ListT m x)
backtrackAlg oalg Empty = empty
backtrackAlg oalg (Nondet xs ys) = pure xs <|> pure ys
backtrackAlg oalg (Once p) = ListT $ do
  mx <- runListT p
  case mx of
    Nothing       -> return Nothing
    Just (x, mxs) -> return (Just (x, empty))



-- | `backtrackOnce` is a handler that transforms nondeterministic effect
-- t`Once` into the t`ListT` monad transformer,
-- supporting backtracking.
backtrackOnce :: Handler '[Once] '[] '[ListT] a [a]
backtrackOnce = handler' runListT' backtrackOnceAlg

-- | `backtrackOnceAlg` defines the semantics of backtracking for the t`Once`
-- effect in the context of the t`ListT` monad transformer.
backtrackOnceAlg
  :: Monad m
  => (forall x . oeff m x -> m x)
  -> (forall x . Effs '[Once] (ListT m) x -> ListT m x)
backtrackOnceAlg oalg op
  | Just (Scp (Once_ p)) <- prj op =
    ListT $ do mx <- runListT p
               case mx of
                 Nothing       -> return Nothing
                 Just (x, mxs) -> return (Just (x, empty))