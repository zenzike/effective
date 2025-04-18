{-|
Module      : Control.Effect.Except
Description : Exception throwing with a value
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Except (
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
  ExceptT(..), runExceptT
) where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped

import Control.Monad.Trans.Except (ExceptT(..), runExceptT)

-- | Signature for throwing exceptions of type @e@.
type Throw e = Alg (Throw_ e)
-- | Underlying signature for throwing exceptions of type @e@.
newtype Throw_ e k where
  Throw :: e -> Throw_ e k
  deriving Functor

-- | Syntax for throwing exceptions of type @e@. This operation is algebraic:
--
{-# INLINE throw #-}
-- > throw e >>= k = throw e
throw :: forall e sig a . (Member (Throw e) sig) => e -> Prog sig a
throw e = call @(Throw e) (Alg (Throw e))

-- | Internal signature for catching exceptions of type @e@.
type Catch e = Scp (Catch_ e)
-- | Underlying signature for catching exceptions of type @e@.
data Catch_ e k where
  Catch :: k -> (e -> k) -> Catch_ e k
  deriving Functor

-- | Syntax for catching exceptions of type @e@. This operation is scoped.
{-# INLINE catch #-}
catch :: forall e sig a . Member (Catch e) sig => Prog sig a -> (e -> Prog sig a) -> Prog sig a
catch p q = call' @(Catch e) (Scp (Catch p q))

-- | The 'except' handler will interpret @catch p q@ by first trying @p@.
-- If it fails, then @q@ is executed.
except :: Handler '[Throw e, Catch e] '[] (ExceptT e) (Either e)
except = handler runExceptT exceptAlg

-- | The algebra for the 'except' handler.
exceptAlg :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Throw e, Catch e] (ExceptT e m) x -> ExceptT e m x)
exceptAlg _ eff
  | Just (Alg (Throw e)) <- prj eff
      = ExceptT (return (Left e))
  | Just (Scp (Catch p q)) <- prj eff
      = ExceptT $
                  do mx <- runExceptT p
                     case mx of
                       Left e  -> runExceptT (q e)
                       Right x -> return (Right x)

-- | The 'retry' handler will interpet @catch p q@  by first trying @p@.
-- If it fails, then @q@ is executed as a recovering clause.
-- If the recovery fails then the computation is failed overall.
-- If the recovery succeeds, then @catch p q@ is attempted again.
retry :: Handler '[Throw e, Catch e] '[] (ExceptT e) (Either e)
retry = handler runExceptT retryAlg

-- | The algebra for the 'retry' handler.
retryAlg :: Monad m
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Throw e, Catch e] (ExceptT e m) x -> ExceptT e m x)
retryAlg _ eff
  | Just (Alg (Throw e)) <- prj eff
      = ExceptT (return (Left e))
  | Just (Scp (Catch p q)) <- prj eff = ExceptT $ loop p q
      where
        loop p q =
          do mx <- runExceptT p
             case mx of
               Left e -> do my <- runExceptT (q e)
                            case my of
                              Left e' -> return (Left e')
                              Right y  -> loop p q
               Right x  -> return (Right x)

