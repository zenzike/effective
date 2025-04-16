{-|
Module      : Control.Effect.Internal.Prog
Description : Program constructors and deconstructors
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE LambdaCase #-}

module Control.Effect.Internal.Prog.ProgDirect (
  -- * Program datatype
  Prog (..), 

  -- * Program constructors
  call, 
  call',
  callK,
  progAlg, 
  weakenProg, 

  -- * Program eliminator
  eval,
  fold,
  ) where
import Control.Effect.Internal.Effs

import Data.HFunctor
#if MIN_VERSION_base(4,18,0)
#else
import Control.Applicative
#endif
import Control.Monad

-- | A program that contains at most the effects in @effs@,
-- to be processed by a handler in the exact order given in @effs@.
data Prog (effs :: [Effect]) a where
  Return :: a -> Prog effs a
  Call  :: forall effs a x
        .  (Effs effs) (Prog effs) x
        -> (x -> Prog effs a)
        -> Prog effs a

-- | Construct a program of type @Prog effs a@ using an operation of type @eff (Prog effs) a@ with
-- an explicit continuation given as a function @a -> (Prog effs b)@.
{-# INLINE callK #-}
callK :: forall eff effs a b . (Member eff effs, HFunctor eff) 
      => eff (Prog effs) a -> (a -> Prog effs b) -> Prog effs b
callK x k = Call (inj x) k

-- | Construct a program of type @Prog effs a@ using an operation of type @eff (Prog effs) (Prog effs a)@, 
-- when @eff@ is a member of @effs@.
{-# INLINE call #-}
call :: forall eff effs a . (Member eff effs, HFunctor eff) => eff (Prog effs) (Prog effs a) -> Prog effs a
call x = Call (inj x) id

-- | A variant of `call` without the explicit continuation argument.
{-# INLINE call' #-}
call' :: forall eff effs a . (Member eff effs, HFunctor eff) => eff (Prog effs) a -> Prog effs a
call' x = Call (inj x) Return

instance Functor (Prog sigs) where
  {-# INLINE fmap #-}
  fmap :: (a -> b) -> Prog sigs a -> Prog sigs b
  fmap f (Return x)  = Return (f x)
  fmap f (Call op k) = Call op (fmap f . k)

instance Applicative (Prog effs) where
  {-# INLINE pure #-}
  pure :: a -> Prog effs a
  pure  = Return

  {-# INLINE (<*>) #-}
  (<*>) :: Prog effs (a -> b) -> Prog effs a -> Prog effs b
  Return f    <*> p = fmap f p
  Call opf kf <*> q = Call opf ((<*> q) . kf)

  {-# INLINE (*>) #-}
  (*>) :: Prog effs a -> Prog effs b -> Prog effs b
  (*>) = liftA2 (const id)

  {-# INLINE (<*) #-}
  (<*) :: Prog effs a -> Prog effs b -> Prog effs a
  (<*) = liftA2 const

  {-# INLINE liftA2 #-}
  liftA2 :: (a -> b -> c) -> Prog effs a -> Prog effs b -> Prog effs c
  liftA2 f (Return x) q    = fmap (f x) q
  liftA2 f (Call opx kx) q = Call opx ((flip (liftA2 f) q) . kx)

instance Monad (Prog effs) where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  Return x   >>= f = f x
  Call op k  >>= f = Call op (k >=> f)

-- | Weaken a program of type @Prog effs a@ so that it can be used in
-- place of a program of type @Prog effs a@, when every @effs@ is a member of @effs'@.
weakenProg :: forall effs effs' a
  . ( Injects effs effs'
    , HFunctor (Effs effs)
    )
  => Prog effs a -> Prog effs' a
weakenProg (Return x)  = Return x
weakenProg (Call op k) = Call (injs @effs @effs' (hmap weakenProg op)) (weakenProg . k)


-- | Evaluate a program using the supplied algebra. This is the
-- universal property from initial monad @Prog sig a@ equipped with
-- the algebra @Eff effs m -> m@.
{-# INLINE eval #-}
eval
  :: forall effs m a . (Monad m, HFunctor (Effs effs))
  => Algebra effs m
  -> Prog effs a -> m a
eval halg (Return x)   = return x
eval halg (Call op k)  = halg (hmap (eval halg) op) >>= eval halg . k

{-
-- Static argument transform:
-- This degrades performance a bit.
eval halg p =
  let eval' :: forall x . Prog effs x -> m x
      eval' p' = case p' of
                   Return x     -> return x
                   Call op hk k ->
                     join . halg . fmap (eval' . k)
                                 . hmap (eval' . hk) $ op
  in eval' p
-}

-- | Fold a program using the supplied generator and algebra. This is the
-- universal property from the underlying GADT.
fold :: forall f effs a . (Functor f, Functor (Effs effs f), HFunctor (Effs effs))
  => (forall x . x -> f x)
  -> (forall x . (Effs effs f) (f x) -> f x)
  -> Prog effs a -> f a
fold gen alg (Return x) = gen x
fold gen alg (Call op k) =
  alg ((fmap (fold gen alg . k) . hmap (fold gen alg)) op)


-- | Attempt to project an operation of type @eff (Prog effs) (Prog effs a)@.
{-# INLINE prjCall #-}
prjCall :: forall eff effs a . Member eff effs => Prog effs a -> Maybe (eff (Prog effs) (Prog effs a))
prjCall (Call op k) = prj (fmap k $ op)
prjCall _           = Nothing

-- | Construct a program from an operation in a union.
{-# INLINE progAlg #-}
progAlg :: Algebra effs (Prog effs) 
progAlg x = Call x return