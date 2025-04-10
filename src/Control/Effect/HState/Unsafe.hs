module Control.Effect.HState.Unsafe (
  Ref,
  Put, Get, New,
  put, get, new,
  Lazy.StateT,
  hstate
) where

import Control.Effect
import GHC.Types (Any)
import Unsafe.Coerce
import qualified Data.Map as M
import qualified Control.Monad.Trans.State.Lazy as Lazy
import Data.HFunctor

type Loc = Int

newtype Ref a = Ref { unRef :: Loc } 

data New (f :: * -> *) (x :: *) where
  New :: a -> (Ref a -> x) -> New f x 

instance Functor f => Functor (New f) where
  fmap f (New a k) = New a (f . k)

instance HFunctor New where
  hmap _ (New a k) = New a k

new :: forall a sig. Member New sig => a -> Prog sig (Ref a)
new a = call' (New a id)

data Put (f :: * -> *) (x :: *) where
  Put :: Ref a -> a -> x -> Put f x 

instance Functor f => Functor (Put f) where
  fmap f (Put r a k) = Put r a (f k)

instance HFunctor Put where
  hmap _ (Put r a k) = Put r a k

put :: forall a sig. Member Put sig => Ref a -> a -> Prog sig ()
put r a = call' (Put r a ())

data Get (f :: * -> *) (x :: *) where
  Get :: Ref a -> (a -> x) -> Get f x 

instance Functor f => Functor (Get f) where
  fmap f (Get r k) = Get r (f . k)

instance HFunctor Get where
  hmap _ (Get r k) = Get r k

get :: forall a sig. Member Get sig => Ref a -> Prog sig a
get r = call' (Get r id)

type Mem = M.Map Loc Any

hstate :: Handler [Put, Get, New] '[] (Lazy.StateT Mem) Identity
hstate = handler (fmap Identity . flip Lazy.evalStateT M.empty) hstateAlg

hstateAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put, Get, New] (Lazy.StateT Mem m) x -> Lazy.StateT Mem m x)
hstateAlg _ op
  | Just (Put r a p) <- prj op =
      do Lazy.modify (\mem -> M.insert (unRef r) (unsafeCoerce a) mem)
         return p

  | Just (Get r p) <- prj @Get op =
      do mem <- Lazy.get
         return (p (unsafeCoerce (mem M.! (unRef r))))

  | Just (New a p) <- prj op =
      do mem <- Lazy.get
         let n = M.size mem
         let mem' = M.insert n (unsafeCoerce a) mem
         Lazy.put mem'
         return (p (Ref n))