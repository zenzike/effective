{-|
Module      : Control.Effect.State.Type
Description : Types for state effect
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Effect.State.Type where

import Control.Effect

$(makeGen [e| put :: forall s. s -> () |])

-- The Template-Haskell splicing above generates the following code.
{-
-- | First-order signature
data Put_ s k where
  Put_ :: s -> k -> Put_ s k
  deriving Functor

-- | Signature for putting a value into the state.
type Put s = Alg (Put_ s)

pattern Put :: Member (Put s) effs => s -> k -> Effs effs m k
pattern Put s k <- (prj -> Just (Alg (Put_ s k)))
  where Put s k = inj (Alg (Put_ s k))

-- | Syntax for putting a value into the state.
{-# INLINE put #-}
put :: Member (Put s) sig => s -> Prog sig ()
put s = call (Alg (Put_ s ()))

{-# INLINE putP #-}
putP :: Member (WithName n (Put s)) sig => Proxy n -> s -> Prog sig ()
putP p s = callP p (Alg (Put_ s ()))

{-# INLINE putN #-}
putN :: forall n -> Member (WithName n (Put s)) sig => s -> Prog sig ()
putN p s = callN p (Alg (Put_ s ()))
-}

$(makeGen [e| get :: forall s. s |])

{-
-- | Underlying signature for getting a value from the state.
newtype Get_ s k where
  Get_ :: (s -> k) -> Get_ s k
  deriving Functor

-- | Signature for getting a value from the state.
type Get s = Alg (Get_ s)

pattern Get :: Member (Get s) effs => (s -> k) -> Effs effs m k
pattern Get k <- (prj -> Just (Alg (Get_ k)))
  where Get k = inj (Alg (Get_ k))

-- | Syntax for getting a value from the state.
{-# INLINE get #-}
get :: Member (Get s) sig => Prog sig s
get = call (Alg (Get_ id))

{-# INLINE getP #-}
getP :: Member (WithName n (Get s)) sig => Proxy n -> Prog sig s
getP p = callP p (Alg (Get_ id))

{-# INLINE getN #-}
getN :: forall n -> Member (WithName n (Get s)) sig => Prog sig s
getN p = callN p (Alg (Get_ id))
-}