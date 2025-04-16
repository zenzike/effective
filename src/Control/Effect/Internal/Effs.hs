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

module Control.Effect.Internal.Effs
  ( Member
  , Members
  , Effect
  , Effs (Effs, Eff)
  , Algebra
  , callM, callM'
  , Injects (..)
  , Append
  , absurdEffs
  , inj
  , prj
  , weakenAlg
  , heither
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
import Data.HFunctor

-- | A variant of `call` for which the effect is on a given monad rather than the `Prog` monad.
{-# INLINE callM #-}
callM :: forall eff effs a m . (Monad m, Member eff effs, HFunctor eff) 
      => Algebra effs m -> eff m (m a) -> m a
callM oalg x = join (oalg (inj x))

-- | A variant of `call'` for which the effect is on a given monad rather than the `Prog` monad.
{-# INLINE callM' #-}
callM' :: forall eff effs a m . (Monad m, Member eff effs, HFunctor eff) 
      => Algebra effs m -> eff m a -> m a
callM' oalg x = oalg (inj x)