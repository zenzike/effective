{-|
Module      : Control.Effect.HOStore.Unsafe
Description : Higher-order store (unsafe implementation)
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides an unsafe implementation of the effect of higher-order store,
that is, mutable state that supports dynamically creation of cells that store values
of /any (lifted) type/.  This implementation is unsafe because references from 
different executions may be wrongly mixed. For example,

@
goWrong :: forall sig. Members '[New, Get, Put] sig => Prog sig Int
goWrong = do iRef <- new @Int 0
             return (handle hstore (get iRef))

-- The following crashes
test :: [Int]
test = handle hstore goWrong
@

Running @handle hstore goWrong@ will crash because the reference @iRef@ is from
the outer @handle hstore@ but it is mistakenly used by the inner program. 

Another way of how things can go wrong is when there is 'multiple-shot algebraic effects':

@
import qualified Control.Effect.State as St
import Control.Effect.Nondet

goWrong2 :: forall sig. 
            Members '[ New, Get, Put, 
                       Choose, 
                       St.Put (Maybe (Ref Int)), St.Get (Maybe (Ref Int))
                     ] sig
         => Prog sig Int
goWrong2 = do iRef <- new @Int 0
              or (do iRef' <- new @Int 0; St.put (Just iRef'); return 0)
                 (do r <- St.get;
                     case r of 
                       Just iRefFromOtherWorld -> get iRefFromOtherWorld
                       Nothing -> return 0)

-- The following crashes
test :: [Int]
test = handle (hstore |> nondet |> St.state_ @(Maybe (Ref Int)) Nothing) goWrong2
@

This goes wrong because higher-order store is handled before non-determinstic 
choices, so different branches of choice have independent memory store, but 
in the first branch, a reference locally to this branch is stored in a global state,
and this reference is de-referenced in the second branch, which has a separate
memory store.

As a rule of thumb for safety, when using the effect handler from this module, 

  1. __never have nested uses of /handle hstore/__,
  2. __never handle higher-order store before any higher-order operations or multiple-shot algebraic operations__. 
  
A safer but more cumbersome interface in the style of ST monad is provided
in the sister module "Control.Effect.HOStore.Safe".
-}
module Control.Effect.HOStore.Unsafe (
  -- * Syntax
  -- ** Operations
  put, get, new,

  -- ** Signatures
  Ref,
  Put, Get, New,

  -- * Semantics
  -- ** Handlers
  hstore,
  St.StateT,
) where

import Control.Effect
import GHC.Types (Any)
import Unsafe.Coerce
import qualified Data.Map as M
import qualified Control.Monad.Trans.State as St
import Data.HFunctor ( HFunctor(..) )

-- | Internally locations in the store are just integers.
type Loc = Int

-- | The type for references storing values of type @a@. This module shall 
-- not export the internal representation of t`Ref`.
newtype Ref a = Ref { unRef :: Loc } 

-- | Signature for the operation of allocating a new memory cell of type @a@. 
-- Note that this is not an ordinary algebraic operation because of the 
-- polymorphic @a@.
data New (f :: * -> *) (x :: *) where
  New :: a -> (Ref a -> x) -> New f x 

instance Functor f => Functor (New f) where
  fmap f (New a k) = New a (f . k)

instance HFunctor New where
  hmap _ (New a k) = New a k

-- | Smart constructor for the t`New` operation.
new :: forall a sig. Member New sig => a -> Prog sig (Ref a)
new a = call' (New a id)

-- | Signature for the operation of updating a memory reference
-- to a new value.
data Put (f :: * -> *) (x :: *) where
  Put :: Ref a -> a -> x -> Put f x 

instance Functor f => Functor (Put f) where
  fmap f (Put r a k) = Put r a (f k)

instance HFunctor Put where
  hmap _ (Put r a k) = Put r a k

-- | Smart constructor for the t`Put` operation.
put :: forall a sig. Member Put sig => Ref a -> a -> Prog sig ()
put r a = call' (Put r a ())

-- | Signature for the operation of reading a memory reference.
data Get (f :: * -> *) (x :: *) where
  Get :: Ref a -> (a -> x) -> Get f x 

instance Functor f => Functor (Get f) where
  fmap f (Get r k) = Get r (f . k)

instance HFunctor Get where
  hmap _ (Get r k) = Get r k

-- | Smart constructor for the t`Get` operation.
get :: forall a sig. Member Get sig => Ref a -> Prog sig a
get r = call' (Get r id)

-- | Internally the store is implemented by a map from locations to 
-- an untyped value. Since the type t`Ref` tracks the type of the
-- value stored, forgetting the types of the values in `Mem` is unproblematic.
type Mem = M.Map Loc Any

-- | The handler for the effect of higher-order store. This handler is not safe
-- and may cause unexpected runtime crashes. Please read the documentation in 
-- the beginning of this module when using it.
hstore :: Handler [Put, Get, New] '[] (St.StateT Mem) Identity
hstore = handler (fmap Identity . flip St.evalStateT M.empty) hstoreAlg

hstoreAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Put, Get, New] (St.StateT Mem m) x -> St.StateT Mem m x)
hstoreAlg _ op
  | Just (Put r a p) <- prj op =
      do St.modify (\mem -> M.insert (unRef r) (unsafeCoerce a) mem)
         return p

  | Just (Get r p) <- prj @Get op =
      do mem <- St.get
         return (p (unsafeCoerce (mem M.! (unRef r))))

  | Just (New a p) <- prj op =
      do mem <- St.get
         let n = M.size mem
         let mem' = M.insert n (unsafeCoerce a) mem
         St.put mem'
         return (p (Ref n))