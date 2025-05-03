{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Gen where

import Control.Effect.CodeGen.Type
import Control.Monad (ap)
import Control.Effect
import Control.Effect.Family.Algebraic

newtype Gen a = Gen { unGen :: forall r. (a -> Up r) -> Up r }

runGen :: Gen (Up a) -> Up a
runGen g = unGen g id

reset :: Gen (Up a) -> Gen (Up a)
reset = return . runGen

shift :: (forall r. (a -> Up r) -> Gen (Up r)) -> Gen a
shift f = Gen $ runGen . f

instance Functor Gen where
  fmap f (Gen m) = Gen (m . (. f))

instance Applicative Gen where
  pure x = Gen (\k -> k x)
  (<*>) = ap

instance Monad Gen where
  return = pure
  m >>= k = Gen (\k' -> unGen m (\a -> unGen (k a) k'))

type CodeGen = Alg Gen

genLet_ :: Up a -> Gen (Up a)
genLet_ c = Gen (\k -> [|| let x = $$c in $$(k [||x||]) ||])

genLetRec_ :: (Up a -> Up a) -> Gen (Up a)
genLetRec_ c = Gen (\k -> [||let x = $$(c [||x||]) in $$(k [||x||])||])

liftGen :: Member CodeGen sig => Gen a -> Prog sig a
liftGen o = call' (Alg o)

genLet :: Member CodeGen sig => Up a -> Prog sig (Up a)
genLet = liftGen . genLet_

genLetRec :: Member CodeGen sig => (Up a -> Up a) -> Prog sig (Up a)
genLetRec = liftGen . genLetRec_