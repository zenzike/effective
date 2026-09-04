{-|
Module      : Control.Effect.State.Operations
Description : Types for state effect
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

In this module we define two operations, @put@ and @get@, for writing and reading
a mutable state. We use our Template Haskell helper `makeGen` to define these
two operations, which is equivalent to writing the following code:

@
-- | First-order signature for @put@
data Put_ s k where
  Put_ :: s -> k -> Put_ s k
  deriving Functor

-- | Higher-order signature for putting a value into the state.
type Put s = Alg (Put_ s)

-- | Pattern synonym for matching a @put@ operation.
pattern Put s k = Alg (Put_ s k)

-- | Invoking the put operation
{-# INLINE put #-}
put :: Member (Put s) effs => s -> Prog effs ()
put s = call (Alg (Put_ s ()))

-- | Invoking the put operation on some @m@ that has an algebra for @put@
{-# INLINE putM #-}
putM :: Member (Put s) effs => Algebra effs m -> s -> m ()
putM alg s = callM alg (Alg (Put_ s ()))

-- | Invoking a named put operation using a proxy argument.
{-# INLINE putP #-}
putP :: Member (n :@ Put s) effs => Proxy n -> s -> Prog effs ()
putP p s = callP p (Alg (Put_ s ()))

-- | Invoking a named put operation using an explicit type argument (since GHC 9.10.1)
{-# INLINE putN #-}
putN :: forall n -> Member (WithName n (Put s)) effs => s -> Prog effs ()
putN p s = callN p (Alg (Put_ s ()))


-- | First-order signature for @get@
data Get_ s k where
  Get_ :: (s -> k) -> Get_ s k
  deriving Functor

-- | Higher-order signature for getting a value from the state.
type Get s = Alg (Get_ s)

-- | Pattern synonym for matching a @get@ operation
pattern Get k = Alg (Get_ k)

-- | Invoking the get operation
{-# INLINE get #-}
get :: member (get s) effs => prog effs s
get = call (Alg (Get_ id))

-- | Invoking the get operation on some @m@ that has an algebra for @get@.
{-# INLINE getM #-}
getM :: Member (Get s) effs => Algebra effs m -> m s
getM alg = callM alg (Alg (Get_ id))

-- | Invoking a named @get@ with a proxy argument.
{-# INLINE getP #-}
getP :: Member (n :@ Get s) effs => Proxy n -> Prog effs s
getP p = callP p (Alg (Get_ id))

-- | Invoking a named @get@ with an explicit type argument (since GHC 9.10.1)
{-# INLINE getN #-}
getN :: forall n -> Member (WithName n (Get s)) effs => Prog effs s
getN p = callN p (Alg (Get_ id))
@
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}

module Control.Effect.State.Operations where

import Control.Effect

$(makeGen [e| put :: forall s. s ~> () |])

$(makeGen [e| get :: forall s. s |])
