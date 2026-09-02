{-# LANGUAGE GeneralizedNewtypeDeriving, AllowAmbiguousTypes, TypeFamilies #-}
{-|
Module      : Control.Effect.Clone
Description : Making copies of an existing effect
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides an \'imitater\' effect that clones an existing effect.
Currently the functionality of this module is very limited: you can only make
one copy of an effect each time, and there is no way to copy an existing
smart constructor.
-}
module Control.Effect.Clone (
  -- * Syntax
  Clone (..),
  clone,
  cloneJ,
  cloneK,
  cloneAlg,
  cloneScp,

  -- * Semantics
  cloneHdl,
) where

import Control.Effect
import Data.List.Kind
import Data.HFunctor
import Unsafe.Coerce
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Data.Kind (Type)
import Control.Effect.Internal.Forward (ForwardM)

-- | Make a copy of an effect signature, which is useful when more than one
-- instances of the same effect are needed in a program.
newtype Clone (eff :: Effect)
              (f   :: Type -> Type)
              (k   :: Type)
              = Clone { unClone :: eff f k } deriving (Functor, HFunctor)

instance ForwardM eff t => Forward (Clone eff) t where
  type FwdConstraint (Clone eff) t = Monad --FwdConstraint eff t
  fwd alg (Clone op) = fwd (alg . Clone) op

-- | Every handler of @effs@ gives rise to a handler of its clone.
cloneHdl :: forall effs oeffs ts a b.
            Handler effs oeffs ts a b
         -> Handler (Map Clone effs) oeffs ts a b
cloneHdl h = unsafeCoerce h  -- There is safer way to do this but this is quicker

-- | Every algebra transformer of @effs@ gives rise to one of its clone.
cloneAT :: forall effs oeffs ts cs.
           AlgTrans effs oeffs ts cs
        -> AlgTrans (Map Clone effs) oeffs ts cs
cloneAT h = unsafeCoerce h

-- | @clone x@ invokes the clone version of the operation @x@.
clone :: forall eff effs a . (HFunctor eff, Member (Clone eff) effs)
      => eff (Prog effs) a -> Prog effs a
clone x = call (Clone x)

-- | @cloneK x k@ invokes the clone version of the operation @x@ (together with its
-- continuation @k@).
cloneK :: forall eff effs a x .
          (HFunctor eff, Member (Clone eff) effs )
       => eff (Prog effs) x
       -> (x -> Prog effs a)
       -> Prog effs a
cloneK x k = callK (Clone x) k

-- | @cloneJ x@ invokes the clone version of the operation @x@ (together with its
-- continuation given as return values).
cloneJ :: forall eff effs a . (HFunctor eff, Member (Clone eff) effs)
      => eff (Prog effs) (Prog effs a) -> Prog effs a
cloneJ x = callJ (Clone x)

-- | A special case of `clone` for algebraic operations.
cloneAlg :: (Member (Clone (Alg f)) effs, Functor f) => f a -> Prog effs a
cloneAlg f = clone (Alg f)

-- | A special case of `clone` for scoped operations.
cloneScp :: (Member (Clone (Scp f)) effs, Functor f) => f (Prog effs a) -> Prog effs a
cloneScp f = clone (Scp f)