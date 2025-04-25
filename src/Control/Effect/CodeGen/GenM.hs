{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.GenM where

import Control.Effect
import Control.Effect.CodeGen.Gen (Gen(..), CodeGen, genLet)
import Control.Effect.CodeGen.Type
import Control.Monad (ap)
import Control.Effect.Algebraic

newtype GenM m a = GenM { unGenM :: forall r. (a -> Up (m r)) -> Up (m r) } 

runGenM :: Monad m => GenM m (Up a) -> Up (m a)
runGenM g = unGenM g (\x -> [|| return $$x ||])

instance Functor (GenM m) where
  fmap f (GenM m) = GenM (m . (. f))

instance Monad m => Applicative (GenM m) where
  pure x = GenM (\k -> k x)
  (<*>) = ap

instance Monad m => Monad (GenM m) where
  return = pure

  m >>= k = GenM (\k' -> unGenM m (\a -> unGenM (k a) k'))

type CodeGenM m = Alg (GenM m)

liftGenM :: forall m sig a. Member (CodeGenM m) sig => GenM m a -> Prog sig a
liftGenM o = call' (Alg o)

genDo_ :: Monad m => Up (m a) -> GenM m (Up a)
genDo_ c = GenM (\k -> [|| do x <- $$c; $$(k [||x||]) ||])

genDo :: (Monad m, Member (CodeGenM m) sig) => Up (m a) -> Prog sig (Up a)
genDo = liftGenM . genDo_

-- | The final answer type of @`GenM` m a@ must be some @m r@ while @`Gen` a@ doesn't
-- have this restriction, so @Gen a@ can be specialised to @Gen M@.
specialise :: Gen a -> GenM m a
specialise g = GenM (unGen g)

-- | As a result of `specialise`, whenever we have an effect @CodeGenM m@, we can
-- use the effect `CodeGen` as well (for example, generating let-bindings using `genLet`).
specialiseGen :: forall m . Handler '[CodeGen] '[CodeGenM m] '[] '[]
specialiseGen = interpret1 $ \(Alg g) -> liftGenM @m (specialise g)