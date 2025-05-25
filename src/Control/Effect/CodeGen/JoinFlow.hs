{-
Module      : Control.Effect.CodeGen.JoinFlow
Description : Join code-generation branches
License     : MIT
Maintainer  : Zhixuan Yang
Stability   : experimental

When using the code-generation effect in meta-programs, we frequently use functions from
"Control.Effect.CodeGen.Split" to split code generation into different branches. Clearly,
splitting too much would lead to blow up of code size. One simple fix is to use the `reset`
operation from "Control.Effect.CodeGen.Up", which binds the current result of code generation
to a let-binding and restart code-generation again (with a single generation branch).

A small flaw of this solution is that it forces all previous generation branches
to share a single \'join point\', and this sometimes forces us to generate
unnecessary wrapping and unwrapping. For example, imagine we have many
code-generation branches, and some of them return values of type @a@ and
all others return values of type @b@.
If we have only one join point, the shared join point has to receive a value of
type @Either a b@, and we need to insert @Left@ and @Right@ in all branches 
to invoke this shared join point. However, there is no reason we can have only
one single join point, we should just generate two joint points (using
let-bindings), one receiving @a@-values and the other receiving @b@-values.

This module provides an operation `joinFlow` to do this automatically. This
technique in this module is described in Section 3.5 of Andras Kovacs's [ICFP
2024 paper](https://dl.acm.org/doi/10.1145/3674648), where the operation is
called @join@.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Effect.CodeGen.JoinFlow where

import Control.Effect
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Split
import Control.Effect.CodeGen.Down
import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.SoPU

import Data.HFunctor
import qualified Data.Iso as Iso

import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State.Strict
import qualified Control.Monad.Trans.State.Lazy as L
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Push
import Control.Monad.Trans.ResumpUp

-- | Signature for the `joinFlow` operation.
data JoinFlow (f :: * -> *) x where
  JoinFlow :: forall y x f. IsSOP y => f y -> (y -> x)  -> JoinFlow f x

instance Functor (JoinFlow f) where
  fmap f (JoinFlow o k) = JoinFlow o (f . k) 

instance HFunctor JoinFlow where
  hmap f (JoinFlow o k) = JoinFlow (f o) k 

-- | If @x@ is a type isomorphic to @(Up a11, ..., a1n1) + .. + (Up an1, ... , Up amn_m)@,
-- @joinFlow p@ creates a join point for each of the summand (each receiving a value of
-- the corresponding product type) and resumes the code generation from these join points.
joinFlow :: forall x sig. (Member JoinFlow sig, IsSOP x) 
         => Prog sig x -> Prog sig x
joinFlow p = call' (JoinFlow p id)

-- | @joinFlow@ on a monad @m@.
joinFlowM :: forall x sig m. Member JoinFlow sig 
          => IsSOP x => Algebra sig m -> m x -> m x
joinFlowM alg p = callM' alg (JoinFlow p id)

-- | Join operation on the monad `Gen`.
joinGenAlg :: Algebra '[JoinFlow] Gen
joinGenAlg = Iso.bwd singAlgIso (\(JoinFlow p k) -> fmap k (joinGen p)) where
  joinGen :: forall a. IsSOP a => Gen a -> Gen a
  joinGen p = shiftGen (\(k :: a -> Up r) -> 
    let fsu = tabulate (singRep @a) (k . decode @a)
    in do f <- genFunSU @_ @r (singRep @a) fsu
          a <- p
          return (index f (encode a)))

-- | Join operation on the monad `GenM m`.
joinGenMAlg :: forall m. Monad m => Algebra '[JoinFlow] (GenM m)
joinGenMAlg = Iso.bwd singAlgIso (\(JoinFlow p k) -> fmap k (joinGenM p)) where
  joinGenM :: forall m a. Monad m => IsSOP a => GenM m a -> GenM m a
  joinGenM p = shiftGenM (\(k :: a -> Up (m r)) -> 
    let fsu = tabulate (singRep @a) (k . decode @a)
    in do f <- specialise (genFunSU @_ @(m r) (singRep @a) fsu)
          a <- p
          return (index f (encode a)))

-- | Algebra transformer for the join operation on `PushT`.
joinPush :: forall m . AlgTrans '[JoinFlow] '[UpOp m, CodeGen] '[PushT] (MonadDown m)
joinPush = algTrans1 $ \oalg (JoinFlow (p :: PushT n y) kV) -> PushT $ \kC (kN :: n (Up t)) ->
 do kn <- genLetM oalg [|| $$(down @n @m kN) ||]
    let fsu cy = [|| \rest -> $$(down @n @m (kC (kV (decode @y cy)) (upM @m oalg [||rest||]))) ||]
    kc <- liftGenA oalg (genFunSU @_ @(m t -> m t) (singRep @y) (tabulate (singRep @y) fsu))
    runPushT p
      (\y mas -> genLetM oalg [|| $$(index kc (encode y)) $$(down @n @m mas) ||] >>= upM @m oalg) 
      (upM oalg kn)

-- | Algebra transformer for the join operation on `ResT`.
joinRes :: forall m s l. (Functor l, forall x. Split (s x) (l (Up x)), l $~> s) 
        => AlgTrans '[JoinFlow] '[UpOp m, CodeGen] '[ResUpT l] (MonadDown m)
joinRes = algTrans1 $ \oalg (JoinFlow (p :: ResUpT l n y) kV) -> 
  ResUpT $ \(kD :: x -> n (Up t)) (kM :: l (n (Up t)) -> n (Up t)) ->
    let sy = singRep @y

        fsu cy = [|| $$(down @n @m (kD (kV (decode @y cy)))) ||]

        aux :: Up (s (m t)) -> Up (m t)
        aux csmt = down @n @m $
          do lcmt <- liftGenA oalg (genSplit @(s (m t)) @(l (Up (m t))) csmt)
             kM (fmap (upM oalg) lcmt)
    in do kd <- liftGenA oalg (genFunSU @_ @(m t) sy (tabulate sy fsu))
          km <- genLetM oalg [||\sm -> $$(aux [||sm||]) ||]
          runResUpT p (\y -> upM @m oalg (index kd (encode y))) 
            (\ln -> upM oalg [|| $$km $$(down @l @s (fmap (down @n @m) ln)) ||])

-- * Forwarders for @JoinFlow@
--
-- Algebra transformers of @JoinFlow@ for other monad transformers take the form
-- @AlgTrans '[JoinFlow] '[JoinFlow]@, so we define them as the default forwarder
-- @JoinFlow@, saving us the trouble of explicitly use them when staging
-- the meta-program.

instance Forward JoinFlow MaybeT where
  type FwdConstraint JoinFlow MaybeT = TruthC
  fwd oalg (JoinFlow p k) = MaybeT $ oalg (JoinFlow (runMaybeT p) (fmap k))

instance Forward JoinFlow (ExceptT (Up e)) where
  type FwdConstraint JoinFlow (ExceptT (Up e))= TruthC
  fwd oalg (JoinFlow p k) = ExceptT $ oalg (JoinFlow (runExceptT p) (fmap k))

instance Forward JoinFlow (StateT (Up s)) where
  type FwdConstraint JoinFlow (StateT (Up s))= TruthC
  fwd oalg (JoinFlow p k) = StateT $ \s -> oalg (JoinFlow (runStateT p s) (\(a,b) -> (k a, b)))

instance Forward JoinFlow (L.StateT (Up s)) where
  type FwdConstraint JoinFlow (L.StateT (Up s))= TruthC
  fwd oalg (JoinFlow p k) = L.StateT $ \s -> oalg (JoinFlow (L.runStateT p s) (\(a,b) -> (k a, b)))

instance Forward JoinFlow (ReaderT (Up s)) where
  type FwdConstraint JoinFlow (ReaderT (Up s))= TruthC
  fwd oalg (JoinFlow p k) = ReaderT $ \s -> oalg (JoinFlow (runReaderT p s) k)

instance Forward JoinFlow (WriterT (Up s)) where
  type FwdConstraint JoinFlow (WriterT (Up s))= TruthC
  fwd oalg (JoinFlow p k) = WriterT $ oalg (JoinFlow (runWriterT p) (\(a,b) -> (k a, b)))

instance Forward JoinFlow (CacheT m) where
  type FwdConstraint JoinFlow (CacheT m) = Monad
  fwd alg op = Iso.bwd cacheConversion (alg (hmap (Iso.fwd cacheConversion) op)) 