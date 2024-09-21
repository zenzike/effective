{-|
Module      : Control.Effect.Internal.Effs.Array
Description : Array based union
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Control.Effect.Internal.Effs.Indexed.Array where
import Control.Effect.Internal.Effs.Indexed.Type

import Data.List.Kind

import GHC.TypeLits
import GHC.Exts

import Control.Monad.ST
import Data.Array.ST
import Data.Array


-- | Injects xeffs yeffs means that all of xeffs is in xyeffs
-- Some other effects may be in xyeffs, so xeffs <= yeffs
class KnownNat (Length xeffs) => Injects xeffs xyeffs where
  injs :: Effs xeffs f a -> Effs xyeffs f a
  ixs :: Array Int Int

instance (KnownNats (EffIndexes xeffs xyeffs), KnownNat (Length xeffs))
  => Injects xeffs xyeffs where
  {-# INLINE injs #-}
  injs (Effn n op) = Effn (ixs @xeffs @xyeffs ! n) op

  {-# INLINE ixs #-}
  ixs = runSTArray $ do arr <- newArray_ (0, m - 1)
                        natVals (proxy# :: Proxy# (EffIndexes xeffs xyeffs)) arr
                        return arr
    where
      m = fromInteger (natVal' (proxy# :: Proxy# (Length xeffs)))

-- | A class that witnesses that all the type level nats @ns@ can be reflected
-- into a value level list. Indexing starts from the end of the list, so that
-- the last element always has index @0@.
class KnownNat (Length ns) => KnownNats (ns :: [Nat]) where
  natVals :: Proxy# ns -> STArray s Int Int -> ST s ()

instance KnownNats '[] where
  {-# INLINE natVals #-}
  natVals _ _ = return ()

instance (KnownNat x, KnownNats xs, KnownNat (Length (x ': xs))) => KnownNats (x ': xs) where
  {-# INLINE natVals #-}
  natVals _ arr = do writeArray arr (fromInteger $ natVal' (proxy# @(Length xs)))
                                    (fromInteger $ natVal' (proxy# @x))
                     natVals (proxy# :: Proxy# xs) arr