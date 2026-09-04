{-|
Module      : Control.Effect.Except
Description : Exception throwing with a value
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module contains the effects @Throw e@ for throwing an exception of
type @e@ and @Catch e@ for catching the effect of type @e@. If you only have
one exception, you may want to use the simpler interface provided by
the module "Control.Effect.Maybe".
-}

module Control.Effect.Except (
  -- * Syntax
  -- ** Operations

  -- | Throwing exceptions of type @e@. This operation is algebraic.
  throw,
  throwM,
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
  except, exceptC,
  retry, retryC,

  -- ** Algebras
  exceptAT,
  retryAT,

  -- ** Underlying monad transformers
  ExceptT(ExceptT), runExceptT
) where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Monad.Trans.Except (ExceptT(..), runExceptT)

$(makeAlg [e| throw :: forall e. e ~> 0 |])

-- | Higher-order signature for catching exceptions of type @e@. The type of
-- the catch operation `catch` is currently not supported by the Template
-- Haskell helper `makeScp`, so we need to define it ourselves.
type Catch e = Scp (Catch_ e)

-- | Underlying first-order signature for catching exceptions of type @e@.
data Catch_ e k where
  Catch_ :: k -> (e -> k) -> Catch_ e k
  deriving Functor

-- | Syntax for catching exceptions of type @e@. This operation is scoped.
{-# INLINE catch #-}
catch :: forall e effs a . Member (Catch e) effs => Prog effs a -> (e -> Prog effs a) -> Prog effs a
catch p q = call @(Catch e) (Scp (Catch_ p q))

pattern Catch :: f k -> (e -> f k) -> Catch e f k
pattern Catch p q = Scp (Catch_ p q)

{-# INLINE catchM #-}
catchM :: forall e effs m a . Member (Catch e) effs => Algebra effs m -> m a -> (e -> m a) -> m a
catchM alg p q = dispatch alg (Scp (Catch_ p q))

-- | A pattern synonym for a catch operation in an effect row.
{-# INLINE catchP #-}
catchP
  :: forall n e effs a.
     Member (n :@ Catch e) effs
  => Proxy n
  -> Prog effs a
  -> (e -> Prog effs a)
  -> Prog effs a
catchP n p q = callP n (Catch p q)

#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
{-# INLINE catchN #-}
catchN
  :: forall n -> forall e effs a.
     Member (n :@ Catch e) effs
  => Prog effs a
  -> (e -> Prog effs a)
  -> Prog effs a
catchN n p q = callN n (Catch p q)
#endif

-- | Underlying implementation of throwing on 'ExceptT'.
{-# INLINE throwAlg #-}
throwAlg :: Monad m => Throw e f k -> ExceptT e m a
throwAlg (Throw e) = ExceptT (return (Left e))

-- | Underlying implementation of catching on 'ExceptT'.
{-# INLINE catchAlg #-}
catchAlg :: Monad m => Catch e (ExceptT e m) a -> ExceptT e m a
catchAlg (Catch p q) = ExceptT $ do
  mx <- runExceptT p
  case mx of
    Left e  -> runExceptT (q e)
    Right x -> return (Right x)

-- | An implementation of catching on 'ExceptT' that after an exception
-- is caught, the program gets retried.
{-# INLINE retryAlg #-}
retryAlg :: Monad m => Catch e (ExceptT e m) a -> ExceptT e m a
retryAlg (Catch p q) = ExceptT $ loop p q where
  loop p q =
    do mx <- runExceptT p
       case mx of
         Left e -> do my <- runExceptT (q e)
                      case my of
                        Left e' -> return (Left e')
                        Right y  -> loop p q
         Right x  -> return (Right x)

-- | The 'except' handler will interpret @catch p q@ by first trying @p@.
-- If it fails, then @q@ is executed.
except :: Handler '[Throw e, Catch e] '[] '[ExceptT e] a (Either e a)
except = Handler (runner' runExceptT) exceptAT

-- | The algebra transformer for the 'except' handler.
exceptAT :: AlgTrans '[Throw e, Catch e] '[] '[ExceptT e] Monad
exceptAT = algTrans' (throwAlg :# catchAlg :# emptyAlg)

-- | The 'retry' handler will interpret @catch p q@ by first trying @p@.
-- If it fails, then @q@ is executed as a recovery clause.
-- If the recovery fails, then the computation fails overall.
-- If the recovery succeeds, then @catch p q@ is attempted again.
retry :: Handler '[Throw e, Catch e] '[] '[ExceptT e] a (Either e a)
retry = handler' runExceptT (throwAlg :#. retryAlg)

-- | The algebra transformer for the 'retry' handler.
retryAT :: AlgTrans '[Throw e, Catch e] '[] '[ExceptT e] Monad
retryAT = algTrans' (throwAlg :#. retryAlg)

-- | Staged version of 'except'
exceptC :: HandlerC '[Throw e, Catch e] '[] '[ExceptT e] a (Either e a)
exceptC = HandlerC
  (RunnerC $ \_ -> [|| runExceptT ||] )
  (AlgTransC $ \_ -> [|| NT throwAlg ||] :#$ [|| NT catchAlg ||] :#$ emptyAlgC)

-- | Staged version of 'retry'
retryC :: HandlerC '[Throw e, Catch e] '[] '[ExceptT e] a (Either e a)
retryC = HandlerC
  (RunnerC $ \_ -> [|| runExceptT ||] )
  (AlgTransC $ \_ -> [|| NT throwAlg ||] :#$ [|| NT retryAlg ||] :#$ emptyAlgC)