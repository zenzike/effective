{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Effect.CodeGen.Join where

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
import Control.Monad.Trans.ResUp

data JoinFlow (f :: * -> *) x where
  JoinFlow :: forall y x f. IsSOP y => f y -> (y -> x)  -> JoinFlow f x

instance Functor (JoinFlow f) where
  fmap f (JoinFlow o k) = JoinFlow o (f . k) 

instance HFunctor JoinFlow where
  hmap f (JoinFlow o k) = JoinFlow (f o) k 

joinFlow :: forall x sig. Member JoinFlow sig 
         => IsSOP x => Prog sig x -> Prog sig x
joinFlow p = call' (JoinFlow p id)

joinFlowM :: forall x sig m. Member JoinFlow sig 
          => IsSOP x => Algebra sig m -> m x -> m x
joinFlowM alg p = callM' alg (JoinFlow p id)

joinFlowM' :: forall x y sig m. Member JoinFlow sig 
           => IsSOP x => Algebra sig m -> m x -> (x -> y) -> m y
joinFlowM' alg p k = callM' alg (JoinFlow p k)

joinGen :: forall a. IsSOP a => Gen a -> Gen a
joinGen p = shiftGen (\(k :: a -> Up r) -> 
  let fsu = tabulate (singRep @a) (k . decode @a)
  in do f <- genFunSU @_ @r (singRep @a) fsu
        a <- p
        return (index f (encode a)))

joinGenAlg :: Algebra '[JoinFlow] Gen
joinGenAlg = Iso.bwd singAlgIso (\(JoinFlow p k) -> fmap k (joinGen p))

joinGenM :: forall m a. Monad m => IsSOP a => GenM m a -> GenM m a
joinGenM p = shiftGenM (\(k :: a -> Up (m r)) -> 
  let fsu = tabulate (singRep @a) (k . decode @a)
  in do f <- specialise (genFunSU @_ @(m r) (singRep @a) fsu)
        a <- p
        return (index f (encode a)))

joinGenMAlg :: forall m. Monad m => Algebra '[JoinFlow] (GenM m)
joinGenMAlg = Iso.bwd singAlgIso (\(JoinFlow p k) -> fmap k (joinGenM p))

joinPush :: forall m . AlgTrans '[JoinFlow] '[UpOp m, CodeGen] '[PushT] (MonadDown m)
joinPush = algTrans1 $ \oalg (JoinFlow (p :: PushT n y) kV) -> PushT $ \kC (kN :: n (Up t)) ->
 do kn <- genLetM oalg [|| $$(down @n @m kN) ||]
    let fsu cy = [|| \rest -> $$(down @n @m (kC (kV (decode @y cy)) (upM @m oalg [||rest||]))) ||]
    kc <- liftGenA oalg (genFunSU @_ @(m t -> m t) (singRep @y) (tabulate (singRep @y) fsu))
    runPushT p 
      (\y mas -> genLetM oalg [|| $$(index kc (encode y)) $$(down @n @m mas) ||] >>= upM @m oalg) 
      (upM oalg kn)

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