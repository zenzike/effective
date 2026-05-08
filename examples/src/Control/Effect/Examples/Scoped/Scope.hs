-- |
-- Module: Control.Effect.Examples.Scoped.Scope
-- Description: A scoped effect and handler which just runs an input program.
-- License: BSD-3-Clause
-- Maintainer: Nicolas Wu
-- Stability: experimental
module Control.Effect.Examples.Scoped.Scope
  ( -- * Syntax

    -- ** Operation
    scope,

    -- * Signature
    Scope,
    Scope_ (..),

    -- * Semantics

    -- ** Handler
    scopeId,

    -- ** Algebra
    scopeIdAT,
  )
where

import Control.Effect
import Control.Effect.Family.Scoped

-- | Underlying signature for the t'Scope' scoped effect.
newtype Scope_ k where
  Scope :: k -> Scope_ k
  deriving (Functor)

-- | Signature for the t'Scope' scoped effect.
type Scope = Scp Scope_

-- | Syntax for running a program using the t'Scope' effect.
{-# INLINE scope #-}
scope :: forall sig a. (Member Scope sig) => Prog sig a -> Prog sig a
scope p = call (Scp (Scope p))

-- | A handler which just runs the program wrapped in 'scope'.
scopeId :: Handler '[Scope] '[] '[] a a
scopeId = handler' id scopeIdAlg

-- | The algebra transformer for the 'scopeId' handler.
scopeIdAT :: AlgTrans '[Scope] '[] '[] Monad
scopeIdAT = AlgTrans scopeIdAlg

-- | The t'Scope'-algebra for the 'scopeId' handler.
scopeIdAlg ::
  (Monad m) =>
  (forall x. oeff m x -> m x) ->
  (forall x. Effs '[Scope] m x -> m x)
scopeIdAlg _ eff
  | Just (Scp (Scope p)) <- prj eff = p
