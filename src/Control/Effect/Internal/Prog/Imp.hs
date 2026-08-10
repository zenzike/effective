{-|
Module      : Control.Effect.Internal.Imp
Description : Programs in impredicative encoding
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides a representation of effectful programs based on impredicative encoding,
which provides good performance for monadic binding and deep handling, but is very bad at
shallow handling (pattern matching). The @effective@ library is all about deep handling, so
the representation from this module is suitable for our purpose.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Internal.Prog.Imp (
  -- * Program datatype
  Prog,

  -- * Program constructors
  call,
  callJ,
  callK,
  progAlg, ProgAlg#,
  weakenProg,

  -- * Program eliminator
  eval, eval'
  )
  where

import Control.Effect.Internal.Algebra

import Data.HFunctor
#if MIN_VERSION_base(4,18,0)
#else
import Control.Applicative
#endif
import Control.Monad
import GHC.Types (Any)
import GHC.TypeLits (natVal, KnownNat, Nat, type (+))
import Unsafe.Coerce (unsafeCoerce)
import Data.Proxy

-- | The impredicative encoding of effectful programs. We work with an array-based
-- representation of algebras for fast access.
newtype Prog (effs :: [Effect]) a =
  Prog { runProg :: forall m . Monad m => AlgebraArray effs m -> m a }

-- | Construct a program of type @Prog effs a@ using an operation @eff@.
{-# INLINE call #-}
call :: forall eff effs a . (Member eff effs, HFunctor eff) => eff (Prog effs) a -> Prog effs a
call x = Prog $ \(alg :: AlgebraArray effs m) ->
  let r :: forall x. Prog effs x -> m x
      r p = runProg p alg
  in callM alg (hmap r x)

-- | @unsafeCall n@ should only be used when @eff@ is the @n@-th element of @effs@.
{-# INLINE unsafeCall #-}
unsafeCall :: forall eff effs a . (HFunctor eff) => Int -> eff (Prog effs) a -> Prog effs a
unsafeCall n x = Prog $ \(alg :: AlgebraArray effs m) ->
  let r :: forall x. Prog effs x -> m x
      r p = runProg p alg
  in unsafeCallM n alg (hmap r x)

-- | A variant of `call` with a continuation argument given as return values.
-- Semantically, @callJ = join . `call`@.
{-# INLINE callJ #-}
callJ
  :: forall eff effs a.
     ( Member eff effs, HFunctor eff )
  => eff (Prog effs) (Prog effs a)
  -> Prog effs a
callJ = join . call

-- | A variant of `call` with a continuation argument given as a function.
-- Semantically, @callK x k = `call` x >>= k@.
{-# INLINE callK #-}
callK
  :: forall eff effs a b.
     ( Member eff effs, HFunctor eff )
  => eff (Prog effs) a
  -> (a -> Prog effs b)
  -> Prog effs b
callK x k = call x >>= k

{-
-- The following is type-safe but its performance is awful.

{-# INLINE progAlg #-}
progAlg :: (KnownEffs effs, Sequence s) => Algebra_ s effs (Prog effs)
progAlg = fromAlgebraArray progAlgArr

{-# INLINE progAlgArr #-}
progAlgArr :: (KnownEffs effs) => AlgebraArray effs (Prog effs)
progAlgArr = Algebra $ makeCases (\op -> Prog $ \(alg :: AlgebraArray effs m) ->
  let r :: forall x. Prog effs x -> m x
      r p = runProg p alg
  in applyAlgebra alg (hmap r op))

-- The following is an unsafe but efficient version of @progAlg@.
-}

type ProgAlg# effs = ProgAlg effs effs 0

progAlg :: forall effs s. (Sequence s, ProgAlg# effs) => Algebra_ s effs (Prog effs)
progAlg = unsafeAlgebra (progAlgAux @effs @effs @0)

class ProgAlg (effs :: [Effect]) (effs' :: [Effect]) (n :: Nat) where
  progAlgAux :: forall s. Sequence s => s Any

instance ProgAlg '[] effs' n where
  progAlgAux = nil

instance (HFunctor eff, KnownNat n, ProgAlg effs effs' (n + 1)) => ProgAlg (eff ': effs) effs' n where
  progAlgAux = unsafeCoerce f `cons` progAlgAux @effs @effs' @(n+1) where
    f :: forall x. eff (Prog effs') x -> Prog effs' x
    f = unsafeCall (fromIntegral $ natVal @n Proxy)

instance Functor (Prog effs) where
  {-# INLINE fmap #-}
  fmap :: (a -> b) -> Prog effs a -> Prog effs b
  fmap f p = Prog $ \alg -> fmap f (runProg p alg)

instance Applicative (Prog effs) where
  {-# INLINE pure #-}
  pure :: a -> Prog effs a
  pure a = Prog $ \alg -> return a

  {-# INLINE (<*>) #-}
  (<*>) :: Prog effs (a -> b) -> Prog effs a -> Prog effs b
  (<*>) = ap

instance Monad (Prog effs) where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  p >>= k = Prog $ \alg -> runProg p alg >>= (\a -> runProg (k a) alg)

-- | Weaken a program of type @Prog effs a@ so that it can be used in place of a
-- program of type @Prog effs' a@, when every effect in @effs@ is a member of @effs'@.
{-# INLINE weakenProg #-}
weakenProg
  :: forall effs effs' a.
     (Members effs effs')
  => Prog effs a
  -> Prog effs' a
weakenProg p = Prog $ \alg -> runProg p (weakenAlg alg)

-- | Evaluate a program using the supplied algebra. This is the universal
-- property of the initial monad @Prog effs a@ equipped with the algebra @Eff effs
-- m -> m@.
{-# INLINE eval #-}
eval
  :: forall effs m a s.
     ( Monad m, Sequence s )
  => Algebra_ s effs m
  -> Prog effs a
  -> m a
eval alg p = runProg p (toAlgebraArray alg)

-- | A specialised version of @eval@, which can be used for helping
-- the type checker to infer the sequence parameter @s@.
{-# INLINE eval' #-}
eval'
  :: forall effs m a.
     (Monad m)
  => Algebra effs m
  -> Prog effs a
  -> m a
eval' alg p = runProg p (toAlgebraArray alg)