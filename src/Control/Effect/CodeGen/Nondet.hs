module Control.Effect.CodeGen.Nondet (pushAT, pushWithUpAT, pushGen) where

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

pushWithUpAT :: Monad m 
         => AlgTrans '[UpOp (ListT m), UpOp [], Empty, Choose, Once] 
                     '[UpOp m] 
                     '[PushT] 
                      (MonadDown m)

pushWithUpAT = weakenC (appendAT upPush pushAT)

pushAT :: AlgTrans '[Empty, Choose, Once] '[] '[PushT] TruthC
pushAT = AlgTrans $ pushAlg where
  pushAlg :: forall n. Algebra '[] n
          -> Algebra '[Empty, Choose, Once] (PushT n)
  pushAlg oalg op
    | (Just (Alg Empty))        <- prj op = empty
    | (Just (Scp (Choose x y))) <- prj op = x <|> y
    | (Just (Scp (Once x)))     <- prj op = P.once x

pushGen :: AlgTrans '[Empty, Choose, Once, UpOp []] '[] '[PushT] ((~) Gen)
pushGen = AlgTrans $ pushAlg where
  pushAlg :: forall n. Algebra '[] n
          -> Algebra '[Empty, Choose, Once, UpOp []] (PushT Gen)
  pushAlg oalg op
    | (Just (Alg Empty))        <- prj op = empty
    | (Just (Scp (Choose x y))) <- prj op = x <|> y
    | (Just (Scp (Once x)))     <- prj op = P.once x
    | (Just (Alg (UpOp o k)))   <- prj op = fmap k (upListPushGenAlg o)