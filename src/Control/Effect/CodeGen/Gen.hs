{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Gen where

import Control.Effect.CodeGen.Type
import Control.Monad (ap)
import Control.Effect
import Control.Effect.Algebraic

--   newtype GenT m a = GenT { runGenT :: forall r. (a -> Up (m r)) -> Up (m r) } 

newtype Gen a = Gen { unGen :: forall r. (a -> Up r) -> Up r }

runGen :: Gen (Up a) -> Up a
runGen g = unGen g id

instance Functor Gen where
  {-# INLINE fmap #-}
  fmap f (Gen m) = Gen (m . (. f))

instance Applicative Gen where
  {-# INLINE pure #-}
  pure x = Gen (\k -> k x)
  {-# INLINE (<*>) #-}
  (<*>) = ap

instance Monad Gen where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  m >>= k = Gen (\k' -> unGen m (\a -> unGen (k a) k'))

type LiftGen = Alg Gen

liftGenAlg :: Algebra '[LiftGen] Gen
liftGenAlg o 
  | Just (Alg o) <- prj o = o

{-# INLINE liftGen #-}
liftGen :: (Member LiftGen sig) => Gen a -> Prog sig a
liftGen o = call' (Alg o)

{-# INLINE genLet #-}
genLet :: (Member LiftGen sig) => Up a -> Prog sig (Up a)
genLet c = liftGen $ Gen (\k -> [||let x = $$c in $$(k [||x||])||])

{-# INLINE genLetRec #-}
genLetRec :: (Member LiftGen sig) => (Up a -> Up a) -> Prog sig (Up a)
genLetRec c = liftGen $ Gen (\k -> [||let x = $$(c [||x||]) in $$(k [||x||])||])