{-|
Module      : Control.Effect.State.Type
Description : Types for state effect
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}

module Control.Effect.State.Type where

import Control.Effect
import Control.Effect.Algebraic

-- | Signature for putting a value into the state.
type Put s = Alg (Put_ s)
-- | Underlying signature for putting a value into the state.
data Put_ s k where
  Put :: s -> k -> Put_ s k
  deriving Functor

-- | Syntax for putting a value into the state.
{-# INLINE put #-}
put :: Member (Put s) sig => s -> Prog sig ()
put s = call (Alg (Put s (return ())))

-- | Signature for getting a value from the state.
type Get s = Alg (Get_ s)

-- | Underlying signature for getting a value from the state.
newtype Get_ s k where
  Get :: (s -> k) -> Get_ s k
  deriving Functor

-- | Syntax for getting a value from the state.
{-# INLINE get #-}
get :: Member (Get s) sig => Prog sig s
get = call (Alg (Get return))

{-# INLINE put' #-}
put' :: Syntax t (Put s) effs => s -> t Identity ()
put' s = mcall (Alg (Put s ()))

type ProgA effs m a = Algebra effs m -> m a

{-# INLINE getA #-}
getA :: forall s m effs . (Monad m, Member (Get s) effs) => ProgAlg effs m s
getA = acall (Alg (Get @s id))

{-# INLINE putA #-}
putA :: forall s m effs . (Monad m, Member (Put s) effs) => s -> ProgAlg effs m ()
putA s = acall (Alg (Put s ()))

{-# INLINE get' #-}
get' :: forall s effs t . Syntax t (Get s) effs => t Identity s
get' = mcall (Alg (Get id))


{-# INLINE putX #-}
putX :: forall s effs t x . (Syntax t (Put s) effs, Reifies x t ) => s -> ProgX x t ()
putX s = xcall (Alg (Put s ()))

{-# INLINE getX #-}
getX :: forall s effs t x . (Syntax t (Get s) effs, Reifies x t ) => ProgX x t s
getX = xcall (Alg (Get id))


{-# INLINE putZ #-}
-- putZ :: forall s effs t . Syntax t (Put s) effs => s -> ProgX' t ()
putZ :: forall s t effs . (MAlgebraZ t effs '[], Functor (t Identity), Member (Put s) effs) => s -> ProgZ t effs ()
putZ s = zcall (Alg (Put s ()))

{-# INLINE getZ #-}
getZ :: forall s t effs . (MAlgebraZ t effs '[], Functor (t Identity), Member (Get s) effs) => ProgZ t effs s
getZ = zcall (Alg (Get id))
-- getZ :: forall s t . (Syntax t (Get s) (IEffs t) ) => ProgX' t s
-- getZ = xcall' (Alg (Get id))

