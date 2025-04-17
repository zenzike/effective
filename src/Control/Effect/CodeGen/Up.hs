{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Up where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Split
import Control.Effect.CodeGen.Gen
import Data.Iso


type UpOp :: (* -> *) -> Effect
type UpOp m = Alg (UpOp_ m)

data UpOp_ (m :: * -> *) (x :: *) where
  UpOp :: Up (m a) -> (Up a -> x) -> UpOp_ m x

-- | An @UpOp m@-operation on a functor @n@ is the same as a function @∀ x. Up (m x) -> n (Up x)@,
-- which is Andras's original formulation of the up operation.
upIso :: forall n m. Functor n => Iso (forall x. UpOp m n x -> n x) (forall x. Up (m x) -> n (Up x))
upIso = Iso fwd bwd where
  fwd :: (forall x. UpOp m n x -> n x) -> (forall x. Up (m x) -> n (Up x))
  fwd o1 umx = o1 (Alg (UpOp umx id))

  bwd :: (forall x. Up (m x) -> n (Up x)) -> (forall x. UpOp m n x -> n x) 
  bwd o2 (Alg (UpOp uma k)) = fmap k (o2 uma)

upAlgIso :: Functor n => Iso (Algebra '[UpOp m] n)  (forall x. Up (m x) -> n (Up x))
upAlgIso = trans singAlgIso upIso 

upGen :: Algebra '[UpOp Identity] Gen
upGen = bwd upAlgIso (\cm -> return [||runIdentity $$cm||])