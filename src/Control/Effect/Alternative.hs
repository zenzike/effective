{-|
Module      : Control.Effect.Alternative
Description : Effects for alternatives with choose and empty.
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Control.Effect.Alternative (
  -- * Syntax
  -- ** Operations

  -- | The operations for alternatives use 'empty' and '<|>' directly
  -- from the 'Control.Applicative.Alternative' type class.
  --
  -- 'empty' is an algebraic operation:
  --
  -- > empty >>= k = empty
  --
  -- '<|>' is a scoped operation.
  empty,

  (<|>),

  -- ** Signatures
  Empty, Empty_(..),
  Choose, Choose_(..),
  Choose', Choose'_(..),

  -- * Semantics
  -- ** Handlers
  alternative,

  -- ** Algebras
  alternativeAlg,
) where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped
import Control.Effect.Internal.MAlgebra
import Control.Monad

import GHC.Exts

import Control.Applicative

-- | Signature for empty alternatives.
type Empty = Alg Empty_
-- | Underlying signature for empty alternatives.
data Empty_ a where
  Empty :: Empty_ a
  deriving Functor

-- | Signature for choice of alternatives.
type Choose = Scp Choose_
-- | Underlying signature for choice of alternatives.
data Choose_ a where
  Choose :: a -> a -> Choose_ a
  deriving Functor

type Choose' = Scp Choose'_
newtype Choose'_ a = Choose' (Bool -> a)
  deriving Functor

choose' :: Choose'_ a -> (a, a)
choose' (Choose' f) = (f True, f False)

-- pattern Choose :: a -> a -> Choose'_ a
-- pattern Choose xs ys <- (choose' -> (xs, ys))
--   where
--     Choose xs ys = Choose' (\b -> if b then xs else ys)


-- | The 'alternative' handler makes use of an 'Alternative' functor @f@
-- as well as a transformer @t@ that produces an 'Alternative' functor @t m@.
-- for any monad @m@ to provide semantics.
{-# INLINE alternative #-}
alternative
  :: forall t f
  . (Monad f, Alternative f
  , forall m . Monad m => Alternative (t m))
  => (forall m . Monad m => (forall a . t m a -> m (f a)))
  -> Handler '[Empty, Choose] '[] t f
alternative run = Handler (\_ -> run) alternativeAlg

-- | The algebra that corresponds to the 'alternative' handler. This uses an
-- underlying 'Alternative' isntance for @t m@ given by a transformer @t@.
{-# INLINE alternativeAlg #-}
alternativeAlg
  :: forall oeffs t m . (Alternative (t m), Functor m)
  => (Algebra oeffs m)
  -> (Algebra [Empty , Choose] (t m))
alternativeAlg oalg eff
  | (Just (Alg Empty))          <- prj eff = empty
  | (Just (Scp (Choose xs ys))) <- prj @Choose @'[Empty, Choose] eff = xs <|> ys

-- | Instance for 'Alternative' that uses 'Choose_ and 'Empty_.
instance (Member Choose sigs, Member Empty sigs)
  => Alternative (Prog sigs) where
  {-# INLINE empty #-}
-- | Syntax for an empty alternative. This is an algebraic operation.
  empty = call (Alg Empty)

  {-# INLINE (<|>) #-}
-- | Syntax for a choice of alternatives. This is a scoped operation.
  xs <|> ys = call (Scp (Choose (fmap return xs) (fmap return ys)))
--   xs <|> ys = call (Scp (Choose (return xs) (return ys)))
--   xs <|> ys = call (Alg (Choose xs ys))

instance (Member Choose effs, Member Empty effs, Monad m)
  => Alternative (ProgAlg effs m) where
  {-# INLINE empty #-}
-- | Syntax for an empty alternative. This is an algebraic operation.
  empty = acall (Alg Empty)

  {-# INLINE (<|>) #-}
-- | Syntax for a choice of alternatives. This is a scoped operation.
  ProgAlg xs <|> ProgAlg ys = ProgAlg (\alg -> alg (inj (Scp (Choose (xs alg) (ys alg)))))

  {-# INLINE some #-}
  some v = some_v
      where
        many_v = some_v <|> pure []
        some_v = liftA2 (:) v many_v

  {-# INLINE many #-}
  many v = many_v
    where
      many_v = some_v <|> pure []
      some_v = liftA2 (:) v many_v

instance (Reifies x t, Member Choose (IEffs t), Member Empty (IEffs t), OEffs t ~ '[], MAlgebra t, Applicative (t Identity))
  => Alternative (ProgX x t) where
  {-# INLINE empty #-}
-- | Syntax for an empty alternative. This is an algebraic operation.
  empty = xcall (Alg Empty)

  {-# INLINE (<|>) #-}
-- | Syntax for a choice of alternatives. This is a scoped operation.
  ProgX xs <|> ProgX ys = xcall (Scp (Choose (xs) (ys)))

instance (Member Choose effs, Member Empty effs, MAlgebraZ t effs '[], Monad (t Identity))
  => Alternative (ProgZ t effs) where
  {-# INLINE empty #-}
-- | Syntax for an empty alternative. This is an algebraic operation.
  empty = zcall (Alg Empty)

  {-# INLINE (<|>) #-}
  xs <|> ys = zcall (Scp (Choose xs ys))
  -- xs <|> ys = zcall' (Scp (Choose (fmap return xs) (fmap return ys)))
  -- xs <|> ys = zcall' (Scp (Choose (return xs) (return ys)))

  {-# INLINE some #-}
  some v = some_v
      where
        many_v = some_v <|> pure []
        some_v = liftA2 (:) v many_v

  {-# INLINE many #-}
  many v = many_v
    where
      many_v = some_v <|> pure []
      some_v = liftA2 (:) v many_v

-- reifyz
-- <<ghc: 1454358328 bytes, 340 GCs, 59832985/270451664 avg/max bytes residency (9 samples), 515M in use, 0.002 INIT (0.002 elapsed), 0.588 MUT (0.536 elapsed), 0.420 GC (0.477 elapsed) :ghc>>
--
-- real    0m1.082s
-- user    0m0.991s
-- sys     0m0.076s

  -- xs <|> ys = (join . zcall) (Scp (Choose (fmap return xs) (fmap return ys)))
  -- xs <|> ys = zcall' (Scp (Choose (fmap return xs) (fmap return ys)))

-- | Syntax for a choice of alternatives. This is a scoped operation.
--   ProgZ xs <|> ProgZ ys = zcall (Scp (Choose (ProgZ xs) (ProgZ ys)))
  -- TODO: should there be an fmap return here like this:
  -- TODO: should there be a fwd instance here perhaps?


-- xs <|> ys = zcall' (Scp (Choose (return xs) (return ys)))
-- <<ghc: 1694525216 bytes, 399 GCs, 59629268/269502296 avg/max bytes residency (9 samples), 515M in use, 0.002 INIT (0.002 elapsed), 0.686 MUT (0.632 elapsed), 0.475 GC (0.532 elapsed) :ghc>>
--
-- real    0m1.233s
-- user    0m1.140s
-- sys     0m0.079s


-- xs <|> ys = zcall' (Scp (Choose (fmap return xs) (fmap return ys)))
-- <<ghc: 1837761000 bytes, 427 GCs, 75198093/340900168 avg/max bytes residency (9 samples), 639M in use, 0.002 INIT (0.002 elapsed), 0.738 MUT (0.673 elapsed), 0.541 GC (0.611 elapsed) :ghc>>
--
-- real    0m1.351s
-- user    0m1.247s
-- sys     0m0.092s