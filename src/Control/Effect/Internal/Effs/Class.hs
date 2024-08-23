{-|
Module      : Control.Effect.Internal.Effs.Class
Description : Class based union
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}

module Control.Effect.Internal.Effs.Class where
import Control.Effect.Internal.Effs.Type

import Data.List.Kind

import GHC.TypeLits
import GHC.Exts

class KnownNat (Length xeffs) => Injects xeffs xyeffs where
  injs :: forall f a . Effs xeffs f a -> Effs xyeffs f a

instance Injects '[] xyseffs where
  {-# INLINABLE injs #-}
  injs = absurdEffs

instance ( KnownNat (Length (xeff ': xeffs))
         , Injects xeffs xyeffs
         , KnownNat (EffIndex xeff xyeffs)
         )
  => Injects (xeff ': xeffs) xyeffs where
  {-# INLINABLE injs #-}
  injs :: forall f a . Effs (xeff ': xeffs) f a -> Effs xyeffs f a
  injs (Effn n op)
    | n == n'   = Effn i' op
    | otherwise = injs @xeffs @xyeffs @f @a  (Effn n op)
    where
      n' = fromInteger (natVal' (proxy# @(Length xeffs)))
      i' = fromInteger (natVal' (proxy# @(EffIndex xeff xyeffs)))
