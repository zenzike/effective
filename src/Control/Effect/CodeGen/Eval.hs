{-|
Module      : Control.Effect.CodeGen.Eval
Description : Evaluating meta-programs into object-level code
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains functions for evaluating meta-programs into object-level
programs. The function `stage` is probably the most useful one.
-}

{-# LANGUAGE TemplateHaskell, MonoLocalBinds, MagicHash #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Control.Effect.CodeGen.Eval where

import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.Operations
import Control.Effect.CodeGen.Down

import Control.Effect
import Control.Effect.Internal.AlgTrans
import Control.Effect.Family.Algebraic
import Control.Effect.Internal.Handler ( HandleM# )
import Data.Functor.Identity
import Data.Iso
import Data.List.Kind
import Language.Haskell.TH.Syntax (Lift (..))

-- | The effects supported by the monad t`Gen`.
type GenEffects = [CodeGen, UpOp Identity]

-- | The algebra of t`Gen`.
genAlg :: Algebra GenEffects Gen
genAlg =
  (\(Alg o :: CodeGen Gen x) -> o) :#.
  (\(up :: UpOp Identity Gen x) -> bwd upIso (\cm -> return [||runIdentity $$cm||]) up)

-- | The effects supported by the monad @`GenM` m@.
type GenMEffects m = [CodeGenM m, CodeGen, UpOp m]

-- | The algebra on t`GenM`.
genMAlg :: forall m. Monad m => Algebra (GenMEffects m) (GenM m)
genMAlg =
  (\(Alg o :: CodeGenM m (GenM m) x) -> o) :#
  (\(Alg o :: CodeGen (GenM m) x) -> specialise o) :#.
  (\(up :: UpOp m (GenM m) x) -> bwd upIso genDo_ up)

type EvalGen# effs oeffs =
  ( WithFwds# effs oeffs GenEffects )

-- | Evaluate a program with an algebra transformer, with t`Gen` at the bottom
-- of monad transformer stack.
evalGen
  :: forall effs oeffs ts cs a.
     ( cs Gen
     , Monad (Apply ts Gen)
     , ForwardsC ((~) Gen) GenEffects ts
     , Members (oeffs `Union` GenEffects) GenEffects
     , EvalGen# effs oeffs )
  => AlgTrans effs oeffs ts cs
  -> Prog (effs `Union` GenEffects) a
  -> Apply ts Gen a
evalGen at = evalAT genAlg (withFwdsAT (Proxy @GenEffects) (weakenCS @((~) Gen) at))

-- | Stage a meta-level program into an object-level monadic computation via t`Gen`.
stage
  :: forall m effs oeffs ts cs a.
     ( cs Gen
     , Monad (Apply ts Gen)
     , ForwardsC ((~) Gen) GenEffects ts
     , Members (oeffs `Union` GenEffects) GenEffects
     , Apply ts Gen $~> m
     , EvalGen# effs oeffs )
  => AlgTrans effs oeffs ts cs
  -> Prog (effs `Union` GenEffects) (CodeQ a)
  -> CodeQ (m a)
stage alg = down . evalGen alg

type EvalGenM# effs oeffs m =
  ( WithFwds# effs oeffs (GenMEffects m) )

-- | Evaluate a program with an algebra transformer, with @GenM m@ at the bottom
-- of monad transformer stack.
evalGenM
  :: forall m effs oeffs ts cs a.
     ( cs (GenM m), Monad m
     , Monad (Apply ts (GenM m))
     , ForwardsC ((~) (GenM m)) (GenMEffects m) ts
     , Members (oeffs `Union` GenMEffects m) (GenMEffects m)
     , EvalGenM# effs oeffs m )
  => AlgTrans effs oeffs ts cs
  -> Prog (effs `Union` GenMEffects m) a
  -> Apply ts (GenM m) a
evalGenM at = evalAT genMAlg (withFwdsAT (Proxy @(GenMEffects m)) (weakenCS @((~) (GenM m)) at))

-- | Stage a meta-level program into an object-level monadic computation via t`GenM`.
stageM
  :: forall m m' effs oeffs ts cs a.
     ( cs (GenM m), Monad m
     , Monad (Apply ts (GenM m))
     , ForwardsC ((~) (GenM m)) (GenMEffects m) ts
     , Members (oeffs `Union` GenMEffects m) (GenMEffects m)
     , Apply ts (GenM m) $~> m'
     , EvalGenM# effs oeffs m )
  => Proxy m
  -> AlgTrans effs oeffs ts cs
  -> Prog (effs `Union` GenMEffects m) (CodeQ a)
  -> CodeQ (m' a)
stageM _ at = down . evalGenM @m at

-- | Handle and run a meta-program, and generate the code. In most cases we don't really
-- want to run the meta-program, so the function `stage` is probably more useful.
stageH
  :: forall effs oeffs ts a b.
     ( Monad (Apply ts Gen)
     , Members oeffs GenEffects
     , ForwardsM GenEffects ts
     , HandleM# effs GenEffects )
  => Handler effs oeffs ts (CodeQ a) (CodeQ b)
  -> Prog (effs `Union` GenEffects) (CodeQ a)
  -> CodeQ b
stageH h p =
  let cb = handleMFwds (Proxy @GenEffects) genAlg h p
  in [|| runIdentity $$(down @Gen @Identity cb) ||]

-- | Handle and run a meta-program, and generate the code. In most cases we don't really
-- want to run the meta-program, so the function `stageM` is probably more useful.
stageHM
  :: forall m effs oeffs ts a b.
     ( Monad (Apply ts (GenM m))
     , Monad m
     , Members oeffs (GenMEffects m)
     , ForwardsM (GenMEffects m) ts
     , HandleM# effs (GenMEffects m) )
  => Handler effs oeffs ts (CodeQ a) (CodeQ b)
  -> Prog (effs `Union` GenMEffects m) (CodeQ a)
  -> CodeQ (m b)
stageHM h p =
  let cb = handleMFwds (Proxy @(GenMEffects m)) genMAlg h p
  in down @(GenM m) @m cb


-- | This is an ad-hoc generalisation of `stageHM'` which allows an additional wrapper @f@
-- in the result type, but multiple layers of wrappers @f1 (f2 (... CodeQ b))@ are not supported.
-- There should be a better way to do this.
stageHM'
  :: forall m f g xeffs yeffs effs oeffs ts a b.
     ( Monad (Apply ts (GenM m))
     , Monad m
     , f $~> g
     , Members oeffs xeffs
     , Members yeffs xeffs
     , ForwardsM yeffs ts
     , HandleM# effs yeffs )
  => Proxy yeffs
  -> Algebra xeffs (GenM m)
  -> Handler effs oeffs ts (CodeQ a) (f (CodeQ b))
  -> Prog (effs `Union` yeffs) (CodeQ a)
  -> CodeQ (m (g b))
stageHM' _ alg h p =
  let cb = handleMFwds (Proxy @yeffs) alg h p
  in down @(GenM m) @m (fmap down cb)

-- | A variant of `stageHM` that works with `Lift`.
stageHML
  :: forall m f g xeffs yeffs effs oeffs ts a b.
     ( Lift a
     , Monad (Apply ts (GenM m))
     , Monad m
     , f $~> g
     , Members oeffs xeffs
     , Members yeffs xeffs
     , ForwardsM yeffs ts
     , HandleM# effs yeffs )
  => Proxy yeffs
  -> Algebra xeffs (GenM m)
  -> Handler effs oeffs ts (CodeQ a) (f (CodeQ b))
  -> Prog (effs `Union` yeffs) a
  -> CodeQ (m (g b))
stageHML _ alg h p =
  let cb = handleMFwds (Proxy @yeffs) alg h (fmap liftTyped p)
  in down @(GenM m) @m (fmap down cb)
