{-|
Module      : Control.Effect.Except
Description : Exception throwing with a value
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

module Control.Effect.Except (
  -- * Syntax
  -- ** Operations

  -- | Throwing exceptions of type @e@. This operation is algebraic.
  throw,
  throwP,
  -- | Catching exceptions of type @e@. This operation is scoped.
  catch,
  catchP,
  catchM,
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
  throwN,
  catchN,
#endif

  -- ** Signatures
  Throw, Throw_(..), pattern Throw,
  Catch, Catch_(..), pattern Catch,

  -- * Semantics
  -- ** Handlers
  except,
  retry,

  -- ** Algebras
  exceptAT,
  retryAT,

  -- ** Underlying monad transformers
  ExceptT(..), runExceptT
) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Monad.Trans.Except (ExceptT(..), runExceptT)

$(makeAlg [e| throw :: forall e. e -> 0 |])

-- | Internal signature for catching exceptions of type @e@.
type Catch e = Scp (Catch_ e)
-- | Underlying signature for catching exceptions of type @e@.
data Catch_ e k where
  Catch_ :: k -> (e -> k) -> Catch_ e k
  deriving Functor

-- | Syntax for catching exceptions of type @e@. This operation is scoped.
{-# INLINE catch #-}
catch :: forall e sig a . Member (Catch e) sig => Prog sig a -> (e -> Prog sig a) -> Prog sig a
catch p q = call @(Catch e) (Scp (Catch_ p q))
-- Unfortunately `makeScp` currently doesn't support operations like `catch` here, which
-- binds a new variable @e -> @ in its second argument.

-- | A pattern synonym for a catch operation in an effect row.
pattern Catch :: Member (Catch e) sigs => f a -> (e -> f a) -> Effs sigs f a
pattern Catch p q <- (prj -> Just (Scp (Catch_ p q))) where
  Catch p q = inj (Scp (Catch_ p q))

{-# INLINE catchM #-}
catchM :: forall e sig m a . Member (Catch e) sig => Algebra sig m -> m a -> (e -> m a) -> m a
catchM alg p q = alg (inj (Scp (Catch_ p q)))

{-# INLINE catchP #-}
catchP :: forall n e sig a . Member (n :@ Catch e) sig
       => Proxy n -> Prog sig a -> (e -> Prog sig a) -> Prog sig a
catchP n p q = callP n (Scp (Catch_ p q))

#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
{-# INLINE catchN #-}
catchN :: forall n -> forall e sig a . Member (n :@ Catch e) sig
       => Prog sig a -> (e -> Prog sig a) -> Prog sig a
catchN n p q = callN n (Scp (Catch_ p q))
#endif

-- | The 'except' handler will interpret @catch p q@ by first trying @p@.
-- If it fails, then @q@ is executed.
except :: Handler '[Throw e, Catch e] '[] '[ExceptT e] a (Either e a)
except = handler' runExceptT exceptAlg

-- | The algebra transformer for the 'except' handler.
exceptAT :: AlgTrans '[Throw e, Catch e] '[] '[ExceptT e] Monad
exceptAT = AlgTrans exceptAlg

exceptAlg :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Throw e, Catch e] (ExceptT e m) x -> ExceptT e m x)
exceptAlg _ (Throw e) = ExceptT (return (Left e))
exceptAlg _ (Catch p q) = ExceptT $ do
  mx <- runExceptT p
  case mx of
    Left e  -> runExceptT (q e)
    Right x -> return (Right x)

-- | The 'retry' handler will interpet @catch p q@  by first trying @p@.
-- If it fails, then @q@ is executed as a recovering clause.
-- If the recovery fails then the computation is failed overall.
-- If the recovery succeeds, then @catch p q@ is attempted again.
retry :: Handler '[Throw e, Catch e] '[] '[ExceptT e] a (Either e a)
retry = handler' runExceptT retryAlg

-- | The algebra transformer for the 'retry' handler.
retryAT :: AlgTrans '[Throw e, Catch e] '[] '[ExceptT e] Monad
retryAT = AlgTrans retryAlg

retryAlg :: Monad m
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Throw e, Catch e] (ExceptT e m) x -> ExceptT e m x)
retryAlg _ (Throw e) = ExceptT (return (Left e))
retryAlg _ (Catch p q) = ExceptT $ loop p q where
  loop p q =
    do mx <- runExceptT p
       case mx of
         Left e -> do my <- runExceptT (q e)
                      case my of
                        Left e' -> return (Left e')
                        Right y  -> loop p q
         Right x  -> return (Right x)