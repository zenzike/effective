-- |
-- Module: Control.Effect.Examples.Scoped.Identity
-- Description: A scoped effect and handler which just runs an input program.
-- License: BSD-3-Clause
-- Maintainer: Nicolas Wu
-- Stability: experimental
module Control.Effect.Examples.Scoped.Identity
  ( -- * Syntax

    -- ** Operation
    identity,

    -- * Signature
    Identity,
    Identity_ (..),

    -- * Semantics

    -- ** Handler
    runIdentity,

    -- ** Algebra
    identityAT,
  )
where

import Control.Effect hiding (Identity, identity)
import Control.Effect.Family.Scoped

-- | Underlying signature for the identity scoped effect.
newtype Identity_ k where
  Identity :: k -> Identity_ k
  deriving (Functor)

-- | Signature for the identity scoped effect.
type Identity = Scp Identity_

-- | Syntax for running a program using the identity effect.
{-# INLINE identity #-}
identity :: forall sig a. (Member Identity sig) => Prog sig a -> Prog sig a
identity p = call (Scp (Identity p))

-- | A handler which just runs the program wrapped in 'identity'.
runIdentity :: Handler '[Identity] '[] '[] a a
runIdentity = handler' id identityAlg

-- | The algebra transformer for the 'runIdentity' handler.
identityAT :: AlgTrans '[Identity] '[] '[] Monad
identityAT = AlgTrans identityAlg

identityAlg ::
  (Monad m) =>
  (forall x. oeff m x -> m x) ->
  (forall x. Effs '[Identity] m x -> m x)
identityAlg _ eff
  | Just (Scp (Identity p)) <- prj eff = p
