{-# LANGUAGE DataKinds, QuantifiedConstraints #-}

module Control.Effect.HState.Safe (
  Ref,
  Put, Get, New,
  put, get, new,
  handleHS,
  handleHSM,
  runHS,
  HSEffs
) where

import Control.Effect
import Control.Monad.Trans.Class
import GHC.Types (Any)
import Unsafe.Coerce
import qualified Data.Map as M
import qualified Control.Monad.Trans.State.Lazy as Lazy
import Data.HFunctor
import Data.List.Kind
import Control.Effect.Internal.Forward

type Loc = Int

newtype Ref w a = Ref { unRef :: Loc } 

data New w (f :: * -> *) (x :: *) where
  New :: a -> (Ref w a -> x) -> New w f x 

instance Functor f => Functor (New w f) where
  fmap f (New a k) = New a (f . k)

instance HFunctor (New w) where
  hmap _ (New a k) = New a k

new :: forall a w sig. Member (New w) sig => a -> Prog sig (Ref w a)
new a = call' (New a id)

data Put w (f :: * -> *) (x :: *) where
  Put :: Ref w a -> a -> x -> Put w f x 

instance Functor f => Functor (Put w f) where
  fmap f (Put r a k) = Put r a (f k)

instance HFunctor (Put w) where
  hmap _ (Put r a k) = Put r a k

put :: forall a w sig. Member (Put w) sig => Ref w a -> a -> Prog sig ()
put r a = call' (Put r a ())

data Get w (f :: * -> *) (x :: *) where
  Get :: Ref w a -> (a -> x) -> Get w f x 

instance Functor f => Functor (Get w f) where
  fmap f (Get r k) = Get r (f . k)

instance HFunctor (Get w) where
  hmap _ (Get r k) = Get r k

get :: forall a w sig. Member (Get w) sig => Ref w a -> Prog sig a
get r = call' (Get r id)

type Mem = M.Map Loc Any

type HSEffs w = '[Put w, Get w, New w]

hstate :: Handler (HSEffs w) '[] (Lazy.StateT Mem) Identity
hstate = handler (fmap Identity . flip Lazy.evalStateT M.empty) (\_ -> hstateAlg)

hstateAlg :: forall m w. 
     Monad m
  => (forall x.  Effs (HSEffs w) (Lazy.StateT Mem m) x -> Lazy.StateT Mem m x)
hstateAlg op
  | Just (Put r a p) <- prj @(Put w) op =
      do Lazy.modify (\mem -> M.insert (unRef r) (unsafeCoerce a) mem)
         return p

  | Just (Get r p) <- prj @(Get w) op =
      do mem <- Lazy.get
         return (p (unsafeCoerce (mem M.! (unRef r))))

  | Just (New a p) <- prj @(New w) op =
      do mem <- Lazy.get
         let n = M.size mem
         let mem' = M.insert n (unsafeCoerce a) mem
         Lazy.put mem'
         return (p (Ref @w n))

runHS :: forall a. (forall w. Prog (HSEffs w) a) -> a
runHS p = handle identity (handleHS p)

handleHS :: forall effs a.  (ForwardEffs effs (Lazy.StateT Mem), HFunctor (Effs effs)) 
              => (forall w. Prog (HSEffs w :++ effs) a) -> Prog effs a
handleHS p = handleMP' hstate p

handleHSM :: forall effs a m.  (ForwardEffs effs (Lazy.StateT Mem), HFunctor (Effs effs), Monad m) 
              => Algebra effs m -> (forall w. Prog (HSEffs w :++ effs) a) -> m a
handleHSM alg p = handleM' alg hstate p

instance (MonadTrans t) => Forward (New w) t where
  fwd oalg (New a k) = lift (oalg (New a k))

instance (MonadTrans t) => Forward (Put w) t where
  fwd oalg (Put r a k) = lift (oalg (Put r a k))

instance (MonadTrans t) => Forward (Get w) t where
  fwd oalg (Get r k) = lift (oalg (Get r k))