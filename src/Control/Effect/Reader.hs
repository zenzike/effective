{-|
Module      : Control.Effect.Reader
Description : Effects for the reader monad
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Reader (
  -- * Syntax
  -- ** Operations
  ask,
  asks,
  local,

  -- ** Signatures
  Ask, Ask_(..),
  Local, Local_(..),

  -- * Semantics
  -- ** Handlers
  reader,

  -- ** Algebras
  readerAlg,

) where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped

import qualified Control.Monad.Trans.Reader as R

-- | Signature for asking for the environment.
type Ask r = Alg (Ask_ r)
-- | Underlying signature for asking for the environment.
data Ask_ r k where
  Ask :: (r -> k) -> Ask_ r k
  deriving Functor

-- | Fetch the value of the environment.
ask :: Member (Ask r) sig => Prog sig r
ask = call (Alg (Ask return))

-- | Retrieve a function of the current environment.
asks :: Member (Ask r) sig
  => (r -> a) -- ^ The selector function to apply to the environment
  -> Prog sig a
asks f = fmap f ask

-- | Signature for 'local' operation
type Local r = Scp (Local_ r)

-- | Underlying signature for 'local' operation
data Local_ r k where
  Local :: (r -> r) -> k -> Local_ r k
  deriving Functor

-- | Execute a computation in a transformed environment
local :: Member (Local r) sig
  => (r -> r)    -- ^ Function to transform the environment
  -> Prog sig a  -- ^ Computation to run in the transformed environment
  -> Prog sig a
local f p = call (Scp (Local f (fmap return p)))

-- | The `reader` handler supplies a static environment @r@ to the program
-- that can be accessed with `ask`, and locally transformed with `local`.
reader :: r -> Handler [Ask r, Local r] '[] (R.ReaderT r) Identity
reader r = handler (fmap Identity . flip R.runReaderT r) readerAlg

-- | The algebra for the 'reader' handler.
readerAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Ask r, Local r] (R.ReaderT r m) x -> R.ReaderT r m x)
readerAlg oalg eff
  | Just (Alg (Ask p)) <- prj eff =
      do r <- R.ask
         return (p r)
  | Just (Scp (Local (f :: r -> r) p)) <- prj eff =
      R.local f p