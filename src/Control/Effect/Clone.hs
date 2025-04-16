{-# LANGUAGE GeneralizedNewtypeDeriving, AllowAmbiguousTypes #-}
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
  cloneK,
  clone, 
  cloneAlg,
  cloneScp,

  -- * Semantics
  cloneHdl,
) where

import Control.Effect
import Data.List.Kind
import Data.HFunctor
import Unsafe.Coerce
import Control.Effect.Algebraic
import Control.Effect.Scoped

-- | Make a copy of an effect signature, which is useful when more than one
-- instances of the same effect are needed in a program.
newtype Clone (eff :: Effect)
              (f   :: * -> *)
              (k   :: *) 
              = Clone { unClone :: eff f k } deriving (Functor, HFunctor)

instance Forward eff t => Forward (Clone eff) t where
  fwd alg (Clone op) = fwd (alg . Clone) op

-- | Every handler of @effs@ gives rise to a handler of its clone.
cloneHdl :: forall effs oeffs t f.
                Handler effs oeffs t f 
             -> Handler (Map Clone effs) oeffs t f
cloneHdl h = unsafeCoerce h  -- There is safer way to do this but this is quicker

-- | @clone x k@ invokes the clone version of the operation @x@ (together with its
-- continuation @k@).
cloneK :: forall eff effs a x . 
          (HFunctor eff, Member (Clone eff) effs )
       => eff (Prog effs) x 
       -> (x -> Prog effs a)
       -> Prog effs a
cloneK x k = callK (Clone x) k

-- | @clone x k@ invokes the clone version of the operation @x@.
clone :: forall eff effs a . (HFunctor eff, Member (Clone eff) effs)
      => eff (Prog effs) (Prog effs a) -> Prog effs a
clone x = call (Clone x)

-- | A special case of `cloneK` for algebraic operations.
cloneAlg :: (Member (Clone (Alg f)) effs, Functor f) => f a -> Prog effs a
cloneAlg f = cloneK (Alg f) return

-- | A special case of `cloneK` for scoped operations.
cloneScp :: (Member (Clone (Scp f)) effs, Functor f) => f (Prog effs a) -> Prog effs a
cloneScp f = cloneK (Scp f) return