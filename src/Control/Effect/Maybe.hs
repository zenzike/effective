{-|
Module      : Control.Effect.Maybe
Description : Exception throwing without a value
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Maybe (
  -- * Syntax
  -- ** Operations
  throw,
  catch,

  -- ** Signatures
  Throw, Throw_(..),
  Catch, Catch_(..),

  -- * Semantics
  -- ** Handlers
  except,
  retry,

  -- ** Algebras
  exceptAlg,
  retryAlg,

  -- ** Underlying monad transformers
  MaybeT(..)
) where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped

import Control.Monad.Trans.Maybe

-- | Signature for throwing exceptions.
type Throw = Alg Throw_
-- | Underlying signature for throwing exceptions.
data Throw_ k where
  Throw :: Throw_ k
  deriving Functor

-- | Syntax for throwing exceptions. This operation is algebraic:
--
-- > throw >>= k = throw
{-# INLINE throw #-}
throw :: Member Throw sig => Prog sig a
throw = call (Alg Throw)

-- | Internal signature for catching exceptions of type @e@.
type Catch = Scp Catch_
-- | Underlying signature for catching exceptions of type @e@.
data Catch_ k where
  Catch :: k -> k -> Catch_ k
  deriving Functor

-- | Syntax for catching exceptions. This operation is scoped.
catch :: Member Catch sig => Prog sig a -> Prog sig a -> Prog sig a
catch p q = call' (Scp (Catch p q))


-- | The 'except' handler will interpret @catch p q@ by first trying @p@.
-- If it fails, then @q@ is executed.
except :: Handler [Throw, Catch] '[] MaybeT Maybe
except = handler runMaybeT exceptAlg

-- | The algebra for the 'except' handler.
exceptAlg :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Throw, Catch] (MaybeT m) x -> MaybeT m x)
exceptAlg _ eff
  | Just (Alg Throw) <- prj eff
      = MaybeT (return Nothing)
  | Just (Scp (Catch p q)) <- prj eff
      = MaybeT $ do mx <- runMaybeT p
                    case mx of
                      Nothing -> runMaybeT q
                      Just x  -> return (Just x)

-- | The 'retry' handler will interpet @catch p q@  by first trying @p@.
-- If it fails, then @q@ is executed as a recovering clause.
-- If the recovery fails then the computation is failed overall.
-- If the recovery succeeds, then @catch p q@ is attempted again.
retry :: Handler [Throw, Catch] '[] MaybeT Maybe
retry = handler runMaybeT retryAlg

-- | The algebra for the 'retry' handler.
retryAlg :: Monad m
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Throw, Catch] (MaybeT m) x -> MaybeT m x)
retryAlg _ eff
  | Just (Alg Throw) <- prj eff
      = MaybeT (return Nothing)
  | Just (Scp (Catch p q)) <- prj eff = MaybeT $ loop p q
      where
        loop p q =
          do mx <- runMaybeT p
             case mx of
               Nothing -> do my <- runMaybeT q
                             case my of
                               Nothing -> return Nothing
                               Just y  -> loop p q
               Just x  -> return (Just x)
