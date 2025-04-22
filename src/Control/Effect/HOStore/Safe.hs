{-# LANGUAGE QuantifiedConstraints, MonoLocalBinds #-}
{-|
Module      : Control.Effect.HOStore.Safe
Description : Higher-order store (safe implementation)
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides the effect of higher-order store, that is, mutable state that 
supports dynamically creation of cells that store values of /any (lifted) type/. 
This module eliminates the problems mentioned in the sister module "Control.Effect.HOStore.Unsafe" 
using a technique similar to Haskell's @ST@ monad. The reference type t`Ref` and the types of the
operations t`Put`, t`New`, t`Get` are all indexed by an additional \'world\' index @w@, and the
handler can only be applied to programs polymorphic in the world parameter.
Currently, @effective@ doesn't have machinery for such /word-indexed/ handlers and operations, so
this module only exports handling functions such as `runHS`, `handleHS`, `handleHSP`, `handleHSM`
without exporting an actual handler that can be combined with other handlers.  This situation may
be changed in future versions of @effective@.

The author conjecture with reasonable confidence that the API exposed by this module is safe (i.e. 
reading/writing a reference always succeeds) when this module is used with any algebraic and scoped
effects (in whatever handling order). But if there are higher-order operations @op@ that are not
scoped operations and these operations @op@ are handled /after/ higher-order store, one should be
careful when defining the forwarder of @op@ along the state monad transformer to ensure that references
created for some memory store are never available to some other memory store. 
(If @op@ is handled /before/ higher-order store, there is nothing to worry about.)
-}
module Control.Effect.HOStore.Safe (
  -- * Syntax
  -- ** Operations
  put, get, new,

  -- ** Signature
  Ref,
  Put, Get, New,
  HSEffs,

  -- * Semantics
  -- ** Handling functions
  runHS,
  handleHS,
  handleHSP,
  handleHSM,
) where

import Control.Effect
import Control.Monad.Trans.Class
import GHC.Types (Any)
import Unsafe.Coerce
import qualified Data.Map as M
import qualified Control.Monad.Trans.State as St
import Data.HFunctor
import Data.List.Kind
#ifdef INDEXED
import GHC.TypeNats
#endif

-- | Internally locations in the store are just integers.
type Loc = Int

-- | The type for references storing values of type @a@ in world @w@.
newtype Ref w a = Ref { unRef :: Loc } 

-- | Signature for the operation of allocating a new memory cell of type @a@ in
-- world @w@.
data New w (f :: * -> *) (x :: *) where
  New :: a -> (Ref w a -> x) -> New w f x 

instance Functor f => Functor (New w f) where
  fmap f (New a k) = New a (f . k)

instance HFunctor (New w) where
  hmap _ (New a k) = New a k

-- | Smart constructor for the t`New` operation.
new :: forall a w sig. Member (New w) sig => a -> Prog sig (Ref w a)
new a = call' (New a id)

-- | Signature for the operation of updating a memory reference
-- to a new value.
data Put w (f :: * -> *) (x :: *) where
  Put :: Ref w a -> a -> x -> Put w f x 

instance Functor f => Functor (Put w f) where
  fmap f (Put r a k) = Put r a (f k)

instance HFunctor (Put w) where
  hmap _ (Put r a k) = Put r a k

-- | Smart constructor for the t`Put` operation.
put :: forall a w sig. Member (Put w) sig => Ref w a -> a -> Prog sig ()
put r a = call' (Put r a ())

-- | Signature for the operation of reading a memory reference.
data Get w (f :: * -> *) (x :: *) where
  Get :: Ref w a -> (a -> x) -> Get w f x 

instance Functor f => Functor (Get w f) where
  fmap f (Get r k) = Get r (f . k)

instance HFunctor (Get w) where
  hmap _ (Get r k) = Get r k

-- | Smart constructor for the t`Get` operation.
get :: forall a w sig. Member (Get w) sig => Ref w a -> Prog sig a
get r = call' (Get r id)

-- | Internal representation of the store.
type Mem = M.Map Loc Any

-- | The effects of higher-order in world @w@.
type HSEffs w = '[Put w, Get w, New w]

-- | The handler of higher-order store. This is not exported because currently
-- effective does not have a world-indexed handdler API. Users of higher-order
-- store now can only use functions such as `handleHSM` exported by this module.
hstore :: Handler (HSEffs w) '[] (St.StateT Mem) Identity
hstore = handler (fmap Identity . flip St.evalStateT M.empty) (\_ -> hstoreAlg)

hstoreAlg :: forall m w. 
     Monad m
  => (forall x.  Effs (HSEffs w) (St.StateT Mem m) x -> St.StateT Mem m x)
hstoreAlg op
  | Just (Put r a p) <- prj @(Put w) op =
      do St.modify (\mem -> M.insert (unRef r) (unsafeCoerce a) mem)
         return p

  | Just (Get r p) <- prj @(Get w) op =
      do mem <- St.get
         return (p (unsafeCoerce (mem M.! (unRef r))))

  | Just (New a p) <- prj @(New w) op =
      do mem <- St.get
         let n = M.size mem
         let mem' = M.insert n (unsafeCoerce a) mem
         St.put mem'
         return (p (Ref @w n))

-- | Running a program with only the effect of higher-order on the empty store, extracting
-- the final pure result.
runHS, handleHS :: forall a. (forall w. Prog (HSEffs w) a) -> a
runHS p = handle identity (handleHSP p)

handleHS = runHS

-- | Running a program with higher-order store and other effects @effs@ on @m@, 
-- resulting in an @m@ program. 
handleHSM :: forall effs a m. 
          ( forall s. Forwards effs (St.StateT s)
#ifdef INDEXED
          , KnownNat (Length effs) 
#endif
          , HFunctor (Effs effs)
          , Monad m
          ) 
          => Algebra effs m -> (forall w. Prog (HSEffs w :++ effs) a) -> m a
handleHSM alg p = handleM' alg hstore p

-- | Running a program with higher-order store and other effects @effs@, resulting
-- in a program with effects @effs@. 
handleHSP :: forall effs a. 
             ( forall s. Forwards effs (St.StateT s)
#ifdef INDEXED
             , KnownNat (Length effs) 
#endif
             , HFunctor (Effs effs)
             ) 
          => (forall w. Prog (HSEffs w :++ effs) a) -> Prog effs a
handleHSP p = handleM' progAlg hstore p

instance (MonadTrans t) => Forward (New w) t where
  fwd oalg (New a k) = lift (oalg (New a k))

instance (MonadTrans t) => Forward (Put w) t where
  fwd oalg (Put r a k) = lift (oalg (Put r a k))

instance (MonadTrans t) => Forward (Get w) t where
  fwd oalg (Get r k) = lift (oalg (Get r k))