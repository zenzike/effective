{-|
Module      : Control.Effect.CodeGen.Gen
Description : The code-generation monad(s)
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental
-}

{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Gen where

import Control.Effect.CodeGen.Type
import Control.Monad (ap)
import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.State.Type

-- * The code-generation monads and their operations

-- | The code-generation monad, which is the codensity monad transformer applied to
-- the type constructor @`Up` :: * -> *@ for code.
newtype Gen a = Gen { unGen :: forall r. (a -> Up r) -> Up r }

-- | The code-generation monad restricted to generate @m@-values.
newtype GenM m a = GenM { unGenM :: forall r. (a -> Up (m r)) -> Up (m r) } 

-- | The final answer type of @t`GenM` m a@ must be some @m r@ while @t`Gen` a@ doesn't
-- have this restriction, so @Gen a@ can be specialised to @GenM m a@.
specialise :: Gen a -> GenM m a
specialise g = GenM (unGen g)

instance Functor Gen where
  fmap f (Gen m) = Gen (m . (. f))

instance Applicative Gen where
  pure x = Gen (\k -> k x)
  (<*>) = ap

instance Monad Gen where
  return = pure
  m >>= k = Gen (\k' -> unGen m (\a -> unGen (k a) k'))

instance Functor (GenM m) where
  fmap f (GenM m) = GenM (m . (. f))

instance Monad m => Applicative (GenM m) where
  pure x = GenM (\k -> k x)
  (<*>) = ap

instance Monad m => Monad (GenM m) where
  return = pure

  m >>= k = GenM (\k' -> unGenM m (\a -> unGenM (k a) k'))

-- | Generate a let-binding.
genLet_ :: Up a -> Gen (Up a)
genLet_ c = Gen (\k -> [|| let x = $$c in $$(k [||x||]) ||])

-- | Generate a recursive let-binding.
genLetRec_ :: (Up a -> Up a) -> Gen (Up a)
genLetRec_ c = Gen (\k -> [||let x = $$(c [||x||]) in $$(k [||x||])||])

-- | Generate a do-binding.
genDo_ :: Monad m => Up (m a) -> GenM m (Up a)
genDo_ c = GenM (\k -> [|| do x <- $$c; $$(k [||x||]) ||])

-- | Execute a code-generating computation. For example, if
--
-- > g :: Up Bool -> Gen (Up Bool)
-- > g b = Gen $ \k -> [|| if $$b then $$(k [||True||]) else $$(k [||False||]) ||]
--
-- Then @runGen (g b)@ evaluates to the code @if $$b then True else False@.
runGen :: Gen (Up a) -> Up a
runGen g = unGen g id

-- | Reset code generation. For example, let @g@ be the function above, then
--
-- > resetGen (g b) = Gen $ \k -> k [|| if $$b then True else False ||]
-- 
-- This is different from @g b@ because @g b@ invokes the continuation @k@ in both
-- branches of the @if@ while @resetGen (g b)@ invokes @k@ only once.
resetGen :: Gen (Up a) -> Gen (Up a)
resetGen = return . runGen

-- | Capture the current continuation.
shiftGen :: (forall r. (a -> Up r) -> Gen (Up r)) -> Gen a
shiftGen f = Gen $ runGen . f

-- | `runGen` for `GenM`.
runGenM :: Monad m => GenM m (Up a) -> Up (m a)
runGenM g = unGenM g (\x -> [|| return $$x ||])

-- | `resetGen` for `GenM`.
resetGenM :: Monad m => GenM m (Up a) -> GenM m (Up a)
resetGenM = genDo_ . runGenM

-- | `shiftGen` for `GenM`.
shiftGenM :: Monad m => (forall r. (a -> Up (m r)) -> GenM m (Up (m r))) -> GenM m a
shiftGenM f = GenM $ (\g -> unGenM g id) . f



-- * Signatures for code-generation operations.

-- | We treat functions @Gen a -> m a@ for a functor @m@ as an (algebraic) operation
-- with signature functor @Gen@.
type CodeGen = Alg Gen

-- | Generic code-generation operation.
liftGen :: Member CodeGen sig => Gen a -> Prog sig a
liftGen o = call' (Alg o)

-- | Generate a let-binding.
genLet :: Member CodeGen sig => Up a -> Prog sig (Up a)
genLet = liftGen . genLet_

-- | Generate a recursive let-binding.
genLetRec :: Member CodeGen sig => (Up a -> Up a) -> Prog sig (Up a)
genLetRec = liftGen . genLetRec_

-- | Perform code generation on a monad @m@.
liftGenA :: Member CodeGen sig => Algebra sig m -> Gen a -> m a
liftGenA alg o = callM' alg (Alg o)

-- | Generate a let-binding on a monad @m@.
genLetM :: forall sig m a . Member CodeGen sig 
        => Algebra sig m -> Up a -> m (Up a) 
genLetM alg = callM' alg . Alg .  genLet_

-- | Generate a recursive let-binding on a monad @m@.
genLetRecM :: forall sig n a . Member CodeGen sig 
           => Algebra sig n -> (Up a -> Up a) -> n (Up a) 
genLetRecM alg = callM' alg . Alg .  genLetRec_

-- | The effect of generating code of type @m a@.
type CodeGenM m = Alg (GenM m)

-- | Generic code-generation operation.
liftGenM :: forall m sig a. Member (CodeGenM m) sig => GenM m a -> Prog sig a
liftGenM o = call' (Alg o)

-- | Generate a do-binding.
genDo :: (Monad m, Member (CodeGenM m) sig) => Up (m a) -> Prog sig (Up a)
genDo = liftGenM . genDo_

-- | Whenever we have an effect @CodeGenM m@, we can use the effect `CodeGen` as
-- well (for example, generating let-bindings using `genLet`).
specialiseGen :: forall m . AlgTrans '[CodeGen] '[CodeGenM m] '[] Monad
specialiseGen = interpretAT1 $ \(Alg g) -> liftGenM @m (specialise g)

-- | Insert a let-binding for every put operation.
letPut :: forall s. AlgTrans '[Put (Up s)] '[Put (Up s), CodeGen] '[] Monad
letPut = interpretAT1 (\(Alg (Put s k)) -> do s' <- genLet s; put s'; return k) 