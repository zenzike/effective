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

module Control.Effect.Internal.Prog where
import Control.Effect.Internal.Effs

import Control.Monad.Trans.Class
import Data.Functor.Identity

import Data.HFunctor
#if MIN_VERSION_base(4,18,0)
#else
import Control.Applicative
#endif
import Control.Monad

-- | A family of programs that may contain at least the effects in @effs@ in any
-- order.
type Progs effs -- ^ A list of effects the program may use
           a    -- ^ The return value of the program
  = forall effs' . Members effs effs' => Prog effs' a

-- TODO: Remove the `Functor` constraint
-- | A program that contains at most the effects in @effs@,
-- to be processed by a handler in the exact order given in @effs@.
data Prog (effs :: [Effect]) a where
  Return :: a -> Prog sigs a
  Call  :: forall sigs a f x
        .  Functor f
        => (Effs sigs) f x
        -> (forall x . f x -> Prog sigs x)
        -> (x -> Prog sigs a)
        -> Prog sigs a

-- The `Call` constructor is an encoding of `Call'` where:
-- Call'   :: (Effs sigs) (Prog sigs) (Prog sigs a) -> Prog sigs a
-- Call' x ~= Call x id return

-- | Construct a program of type @Prog effs a@ using an operation of type @eff (Prog effs) (Prog effs a)@, when @eff@ is a member of @effs@.
{-# INLINE call #-}
call :: forall eff effs a . (Member eff effs, HFunctor eff) => eff (Prog effs) (Prog effs a) -> Prog effs a
call x = Call (inj x) id id

-- call'   :: (Effs sigs) (Prog sigs) (Prog sigs a) -> Prog sigs a
call' :: Algebra effs (Prog effs)
call' x = Call x id return

call'' :: forall eff effs x . (Member eff effs, HFunctor eff)
  => eff (Prog effs) x -> (Prog effs) x
call'' x =  Call (inj @eff @effs x) id return

-- call' :: forall eff effs a . (ProgMonad prog, Member eff effs, HFunctor eff) => eff (prog effs) (prog effs a) -> prog effs a
-- call' x = Call (inj x) id id

instance Functor (Prog sigs) where
  {-# INLINE fmap #-}
  fmap :: (a -> b) -> Prog sigs a -> Prog sigs b
  fmap f (Return x)     = Return (f x)
  fmap f (Call op hk k) = Call op hk (fmap f . k)

instance Applicative (Prog effs) where
  {-# INLINE pure #-}
  pure :: a -> Prog effs a
  pure  = Return

  {-# INLINE (<*>) #-}
  (<*>) :: Prog effs (a -> b) -> Prog effs a -> Prog effs b
  Return f        <*> p = fmap f p
  Call opf hkf kf <*> q = Call opf hkf ((<*> q) . kf)

  {-# INLINE (*>) #-}
  (*>) :: Prog effs a -> Prog effs b -> Prog effs b
  (*>) = liftA2 (const id)

  {-# INLINE (<*) #-}
  (<*) :: Prog effs a -> Prog effs b -> Prog effs a
  (<*) = liftA2 const

  {-# INLINE liftA2 #-}
  liftA2 :: (a -> b -> c) -> Prog effs a -> Prog effs b -> Prog effs c
  liftA2 f (Return x) q        = fmap (f x) q
  liftA2 f (Call opx hkx kx) q = Call opx hkx ((flip (liftA2 f) q) . kx)

instance Monad (Prog effs) where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  Return x      >>= f = f x
  Call op hk k  >>= f = Call op hk (k >=> f)

-- | Weaken a program of type @Prog effs a@ so that it can be used in
-- place of a program of type @Prog effs a@, when every @effs@ is a member of @effs'@.
weakenProg :: forall effs effs' a
  .  Injects effs effs'
  => Prog effs a -> Prog effs' a
weakenProg (Return x) = Return x
weakenProg (Call op hk k)   =
    Call (injs op) (weakenProg @effs @effs' . hk) (weakenProg @effs @effs' . k)

-- | Evaluate a program using the supplied algebra. This is the
-- universal property from initial monad @Prog sig a@ equipped with
-- the algebra @Eff effs m -> m@.
{-# INLINABLE eval #-}
eval :: forall effs m a . Monad m
  => Algebra effs m
  -> Prog effs a -> m a
eval halg (Return x) = return x
eval halg (Call op hk k)  =
    join . halg . fmap (eval halg . k) . hmap (eval halg . hk) $ op
    -- This version is marginally slower:
    -- join . halg . hmap (eval halg . hk) . fmap (eval halg . k) $ op

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

-- This version does slightly better, but still worse than with no SAT
eval halg op =
  let eval' :: Prog effs a -> m a
      eval' op' = case op' of
                    Return x              -> return x
                    Call (Effn n op) hk k ->
                      join . halg $ fmap (eval' . k) $ hmap (eval'' . hk) $ Effn n op

      eval'' :: forall x . Prog effs x -> m x
      eval'' op' = case op' of
                     Return x -> return x
                     Call (Effn n op) hk k ->
                       join . halg $ fmap (eval'' . k) $ hmap (eval'' . hk) $ Effn n op
  in eval' op
-}

-- | Fold a program using the supplied generator and algebra. This is the
-- universal property from the underlying GADT.
fold :: forall f effs a . Functor f
  => (forall x . (Effs effs f) (f x) -> f x)
  -> (forall x . x -> f x)
  -> Prog effs a -> f a
fold falg gen (Return x) = gen x
fold falg gen (Call op hk k) =
  falg ((fmap (fold falg gen . k) . hmap (fold falg gen . hk)) op)


-- | Attempt to project an operation of type @eff (Prog effs) (Prog effs a)@.
{-# INLINE prjCall #-}
prjCall :: forall eff effs a . Member eff effs => Prog effs a -> Maybe (eff (Prog effs) (Prog effs a))
prjCall (Call op hk k) = prj (hmap hk . fmap k $ op)
prjCall _              = Nothing

-- | Construct a program from an operation in a union.
{-# INLINE progAlg #-}
progAlg :: Effs sig (Prog sig) a -> Prog sig a
progAlg x = Call x id return


-- | The higher-order free monad transformer
newtype ProgT effs m a = ProgT { runProgT :: m (ProgF effs m a) }
  deriving Functor
data ProgF effs m a where
  ReturnF :: a -> ProgF effs m a
  CallF   ::
       (Effs effs) f x
    -> (forall x . f x -> ProgT effs m x)
    -> (x -> ProgT effs m a)
    -> ProgF effs m a
--  CallF'   :: (Effs effs) (ProgT effs m) (ProgT effs m a) -> ProgF effs m a

instance Functor m => Functor (ProgF effs m) where
  fmap :: (a -> b) -> ProgF effs m a -> ProgF effs m b
  fmap f (ReturnF x)      =  ReturnF (f x)
  fmap f (CallF op hk k)  =  CallF op hk (fmap f . k)

instance Applicative m => Applicative (ProgT effs m) where
  pure = ProgT . pure . pure

  ProgT mf <*> ProgT mx = ProgT (fmap (<*>) mf <*> mx)

instance Applicative m => Applicative (ProgF effs m) where
  pure = ReturnF

  ReturnF f     <*> ReturnF x      = ReturnF (f x)
  ReturnF f     <*> CallF op hk k  = CallF op hk (fmap f . k)
  CallF op hk k <*> mx             = CallF op hk ((<*> ((ProgT . pure) mx)) . k)

instance Monad m => Monad (ProgT effs m) where
  return = pure

  ProgT mx >>= f  =  ProgT (mx >>= go) where
    go (ReturnF x)      = runProgT (f x)
    go (CallF op hk k)  = return (CallF op hk ((>>= f) . k))

instance Monad m => Monad (ProgF effs m) where
    return = pure

    ReturnF x     >>= f  = f x
    -- CallF op hk k >>= f  = CallF op hk ((>>= ProgF . pure . f) . k)
    CallF op hk k >>= f  = CallF op hk (k >=> ProgT . pure . f)

instance MonadTrans (ProgT effs) where
  lift :: Monad m => m a -> ProgT effs m a
  lift mx = ProgT (fmap pure mx)

toProgT :: forall effs a . Prog effs a -> ProgT effs Identity a
toProgT (Return x)     = return x
toProgT (Call op hk k) = ProgT (Identity (CallF op (toProgT . hk) (toProgT . k)))

-- fromProgT :: ProgT effs Identity a -> Prog effs a
-- fromProgT (ProgT (Identity (ReturnF x)))     = Return x
-- fromProgT (ProgT (Identity (CallF op hk k))) = Call op (fromProgT . hk) (fromProgT . k)
