{-|
Module      : Control.Effect.CodeGen.Gen
Description : The code-generation monad(s)
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains the code-generation monads t'Gen'/t'GenM' and some basic operations
for code generation, such as generating let-bindings.
-}

{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Gen where

import Control.Effect.CodeGen.Operations
import Control.Monad (ap)
import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.State.Operations

-- * The code-generation monads and their operations

-- | The code-generation monad, which is the codensity monad transformer applied to
-- the type constructor @`CodeQ` :: Type -> Type@ for code.
newtype Gen a = Gen { unGen :: forall r. (a -> CodeQ r) -> CodeQ r }

-- | The code-generation monad restricted to generating @m@ values.
newtype GenM m a = GenM { unGenM :: forall r. (a -> CodeQ (m r)) -> CodeQ (m r) }

-- | The final answer type of @t'GenM' m a@ must be some @m r@ while @t'Gen' a@ doesn't
-- have this restriction, so @t'Gen' a@ can be specialised to @t'GenM' m a@.
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
genLet_ :: CodeQ a -> Gen (CodeQ a)
genLet_ c = Gen (\k -> [|| let x = $$c in $$(k [||x||]) ||])

-- | Generate a recursive let-binding.
genLetRec_ :: (CodeQ a -> CodeQ a) -> Gen (CodeQ a)
genLetRec_ c = Gen (\k -> [||let x = $$(c [||x||]) in $$(k [||x||])||])

-- | Generate a do-binding.
genDo_ :: Monad m => CodeQ (m a) -> GenM m (CodeQ a)
genDo_ c = GenM (\k -> [|| do x <- $$c; $$(k [||x||]) ||])

-- | Execute a code-generating computation. For example, if
--
-- > g :: CodeQ Bool -> Gen (CodeQ Bool)
-- > g b = Gen $ \k -> [|| if $$b then $$(k [||True||]) else $$(k [||False||]) ||]
--
-- Then @runGen (g b)@ evaluates to the code @if $$b then True else False@.
runGen :: Gen (CodeQ a) -> CodeQ a
runGen g = unGen g id

-- | Reset code generation. For example, let @g@ be the function above, then
--
-- > resetGen (g b) = Gen $ \k -> k [|| if $$b then True else False ||]
--
-- This is different from @g b@ because @g b@ invokes the continuation @k@ in both
-- branches of the @if@ while @resetGen (g b)@ invokes @k@ only once.
resetGen :: Gen (CodeQ a) -> Gen (CodeQ a)
resetGen = return . runGen

-- | Capture the current continuation.
shiftGen :: (forall r. (a -> CodeQ r) -> Gen (CodeQ r)) -> Gen a
shiftGen f = Gen $ runGen . f

-- | `runGen` for t'GenM'.
runGenM :: Monad m => GenM m (CodeQ a) -> CodeQ (m a)
runGenM g = unGenM g (\x -> [|| return $$x ||])

-- | `resetGen` for t'GenM'.
resetGenM :: Monad m => GenM m (CodeQ a) -> GenM m (CodeQ a)
resetGenM = genDo_ . runGenM

-- | `shiftGen` for t'GenM'.
shiftGenM :: Monad m => (forall r. (a -> CodeQ (m r)) -> GenM m (CodeQ (m r))) -> GenM m a
shiftGenM f = GenM $ (\g -> unGenM g id) . f



-- * Signatures for code-generation operations.

-- | We treat functions @Gen a -> m a@ for a functor @m@ as an (algebraic) operation
-- with signature functor @Gen@.
type CodeGen = Alg Gen

-- | Generic code-generation operation.
liftGen :: Member CodeGen effs => Gen a -> Prog effs a
liftGen o = call (Alg o)

-- | Generate a let-binding.
genLet :: Member CodeGen effs => CodeQ a -> Prog effs (CodeQ a)
genLet = liftGen . genLet_

-- | Generate a recursive let-binding.
genLetRec :: Member CodeGen effs => (CodeQ a -> CodeQ a) -> Prog effs (CodeQ a)
genLetRec = liftGen . genLetRec_

-- | Perform code generation on a monad @m@. By our usual naming convention this
-- function should be called @liftGenM@ because it is a version of @liftGen@ on
-- a monad @m@, but here we already have t'GenM' and `liftGenM`, so this function
-- has to be called something else.
liftGenA :: Member CodeGen effs => Algebra effs m -> Gen a -> m a
liftGenA alg o = callM alg (Alg o)

-- | Generate a let-binding on a monad @m@.
genLetM
  :: forall effs m a.
     Member CodeGen effs
  => Algebra effs m
  -> CodeQ a
  -> m (CodeQ a)
genLetM alg = callM alg . Alg .  genLet_

-- | Generate a recursive let-binding on a monad @m@.
genLetRecM
  :: forall effs n a.
     Member CodeGen effs
  => Algebra effs n
  -> (CodeQ a -> CodeQ a)
  -> n (CodeQ a)
genLetRecM alg = callM alg . Alg .  genLetRec_

-- | The effect of generating code of type @m a@.
type CodeGenM m = Alg (GenM m)

-- | Generic code-generation operation.
liftGenM :: forall n effs a. Member (CodeGenM n) effs => GenM n a -> Prog effs a
liftGenM o = call (Alg o)

-- | Generic code-generation operation.
liftGenMM :: forall m n effs a. Member (CodeGenM n) effs => Algebra effs m -> GenM n a -> m a
liftGenMM alg o = callM alg (Alg o)

-- | Generate a do-binding.
genDo :: (Monad n, Member (CodeGenM n) effs) => CodeQ (n a) -> Prog effs (CodeQ a)
genDo = liftGenM . genDo_

-- | Generate a do-binding for a monad supporting code-generation.
genDoM :: (Monad n, Member (CodeGenM n) effs) => Algebra effs m -> CodeQ (n a) -> m (CodeQ a)
genDoM alg = liftGenMM alg . genDo_

-- | Whenever we have an effect @CodeGenM m@, we can use the effect `CodeGen` as
-- well (for example, generating let-bindings using `genLet`).
specialiseGen :: forall m . AlgTrans '[CodeGen] '[CodeGenM m] '[] Monad
specialiseGen = interpretAT1 $ \(Alg g) -> liftGenM @m (specialise g)

-- | Insert a let-binding for every put operation.
letPut :: forall s. AlgTrans '[Put (CodeQ s)] '[Put (CodeQ s), CodeGen] '[] Monad
-- letPut = interpretAT1 (\(Alg (Put_ s k)) -> do s' <- genLet s; put s'; return k)
letPut = interpretAT1 (\(Put (s :: CodeQ s) k) -> do s' <- genLet s; put s'; return k)