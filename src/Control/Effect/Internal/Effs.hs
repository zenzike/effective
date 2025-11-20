{-|
Module      : Control.Effect.Internal.Effs
Description : The union type for effect operations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ImpredicativeTypes #-}


module Control.Effect.Internal.Effs
  ( Member
  , Members
  , Effect
  , Effs (Effs, Eff)
  , Algebra
  , callM, callJM, callKM
  , singAlgIso
  , Injects (..)
  , Append
  , absurdEffs
  , inj
  , prj
  , weakenAlg
  , heither
  , hcons
  , hunion
  , (#)
  )
  where

#ifdef INDEXED
import Control.Effect.Internal.Effs.Indexed
#else
import Control.Effect.Internal.Effs.Sum
#endif

import Control.Monad
import Data.Iso

-- | A variant of `call'` for which the effect is on a given monad rather than the `Prog` monad.
{-# INLINE callM #-}
callM :: forall eff effs a m . Member eff effs
      => Algebra effs m -> eff m a -> m a
callM oalg x = oalg (inj x)

-- | A variant of `callJ` for which the effect is on a given monad rather than the `Prog` monad.
{-# INLINE callJM #-}
callJM :: forall eff effs a m . (Monad m, Member eff effs)
      => Algebra effs m -> eff m (m a) -> m a
callJM oalg x = join (oalg (inj x))

-- | A variant of `callK'` for which the effect is on a given monad rather than the `Prog` monad.
{-# INLINE callKM #-}
callKM :: forall eff effs a b m . (Monad m, Member eff effs)
      => Algebra effs m -> eff m a -> (a -> m b) -> m b
callKM oalg x k = oalg (inj x) >>= k

-- | An obvious isomorphism between two representations of an algebra for a single effect @eff@.
{-# INLINE singAlgIso #-}
singAlgIso ::
#ifdef INDEXED
  forall eff m. HFunctor eff =>
#endif
  Iso  (Algebra '[eff] m) (forall x. eff m x -> m x)

singAlgIso = Iso fwd bwd where
  {-# INLINE fwd #-}
  fwd :: Algebra '[eff] m -> (forall x. eff m x -> m x)
  fwd alg e = alg (Eff e)

  {-# INLINE bwd #-}
  bwd :: (forall x. eff m x -> m x) -> Algebra '[eff] m
  bwd alg (Eff e) = alg e

