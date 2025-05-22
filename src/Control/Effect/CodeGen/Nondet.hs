{-|
Module      : Control.Effect.CodeGen.Nondet
Description : Algebra transformers for staging nondeterminism
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains algebra transformers for `PushT`, the monad transformer to be
used at the meta level for nondeterminism. The monad transformer `PushT` supports the
usual non-deterministic operations and can be downed to and upped from `ListT`. 
-}
module Control.Effect.CodeGen.Nondet (pushAT, pushWithUpAT, pushGen, upPush) where

import Control.Effect
import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Down
import Control.Effect.Nondet
import Control.Monad.Trans.Push as P

-- | Algebra  of the non-deterministic operations on `PushT`.
pushAT :: AlgTrans '[Empty, Choose, Once] '[] '[PushT] TruthC
pushAT = AlgTrans $ pushAlg where
  pushAlg :: forall n. Algebra '[] n
          -> Algebra '[Empty, Choose, Once] (PushT n)
  pushAlg oalg op
    | (Just (Alg Empty))        <- prj op = empty
    | (Just (Scp (Choose x y))) <- prj op = x <|> y
    | (Just (Scp (Once x)))     <- prj op = P.once x

-- | Algebra of the non-deterministic operations and the up-operation on `PushT`.
pushWithUpAT :: Monad m =>
  AlgTrans '[UpOp (ListT m), UpOp [], Empty, Choose, Once] 
           '[UpOp m] 
           '[PushT] 
            (MonadDown m)
pushWithUpAT = weakenC (appendAT upPush pushAT)

-- | Algebra of the non-deterministic operations and the
-- up-operation on @PushT Gen@.
pushGen :: AlgTrans '[Empty, Choose, Once, UpOp []] '[] '[PushT] ((~) Gen)
pushGen = AlgTrans $ pushAlg where
  pushAlg :: forall n. Algebra '[] n
          -> Algebra '[Empty, Choose, Once, UpOp []] (PushT Gen)
  pushAlg oalg op
    | (Just (Alg Empty))        <- prj op = empty
    | (Just (Scp (Choose x y))) <- prj op = x <|> y
    | (Just (Scp (Once x)))     <- prj op = P.once x
    | (Just (Alg (UpOp o k)))   <- prj op = fmap k (upListPushGenAlg o)