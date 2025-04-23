{-|
Module      : Control.Effect.Internal.ProgImp
Description : Programs in impredicatie encoding
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides a representation of effectful programs based on impredicative encoding,
which provides good performance for monadic binding and deep handling, but is very bad at
shallow handling (pattern matching). The @effective@ library emphasises deep handling, so  
the representation from this module is suitable for our purpose.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE LambdaCase #-}

module Control.Effect.Internal.Prog.ProgImp (
  -- * Program datatype
  Prog, 

  -- * Program constructors
  call, 
  call', 
  callK,
  progAlg, 
  weakenProg, 

  -- * Program eliminator
  eval,
  ) 
  where
import Control.Effect.Internal.Effs

import Data.HFunctor
#if MIN_VERSION_base(4,18,0)
#else
import Control.Applicative
#endif
import Control.Monad

newtype Prog (effs :: [Effect]) a = Prog { runProg :: forall m. Monad m => Algebra effs m -> m a }

-- | Construct a program of type @Prog effs a@ using an operation of type @eff (Prog effs) (Prog effs a)@, 
-- when @eff@ is a member of @effs@.
{-# INLINE call #-}
call :: forall eff effs a . (Member eff effs, HFunctor eff) => eff (Prog effs) (Prog effs a) -> Prog effs a
call x = Prog $ \(alg :: Algebra effs m) ->
  let r :: forall x. Prog effs x -> m x
      r p = runProg p alg 
  in join (alg (inj (fmap r (hmap r x))))

-- | A variant of `call` without the explicit continuation argument.
{-# INLINE call' #-}
call' :: forall eff effs a . (Member eff effs, HFunctor eff) => eff (Prog effs) a -> Prog effs a
call' x = Prog $ \(alg :: Algebra effs m) ->
  let r :: forall x. Prog effs x -> m x
      r p = runProg p alg 
  in alg (inj (hmap r x))

-- | A variant of `call` where the continuation is given as a function.
{-# INLINE callK #-}
callK :: forall eff effs a b . (Member eff effs, HFunctor eff) 
      => eff (Prog effs) a -> (a -> Prog effs b) -> Prog effs b
callK x k = call' x >>= k

-- | Construct a program from an operation in a union.
{-# INLINE progAlg #-}
progAlg :: forall effs. HFunctor (Effs effs) => Algebra effs (Prog effs) 
progAlg x = Prog $ \(alg :: Algebra effs m) ->
  let r :: forall x. Prog effs x -> m x
      r p = runProg p alg 
  in alg (hmap r x)

instance Functor (Prog sigs) where
  {-# INLINE fmap #-}
  fmap :: (a -> b) -> Prog sigs a -> Prog sigs b
  fmap f p = Prog $ \alg -> fmap f (runProg p alg)

instance Applicative (Prog effs) where
  {-# INLINE pure #-}
  pure :: a -> Prog effs a
  pure a = Prog $ \alg -> return a

  {-# INLINE (<*>) #-}
  (<*>) :: Prog effs (a -> b) -> Prog effs a -> Prog effs b
  (<*>) = ap

instance Monad (Prog effs) where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  p >>= k = Prog $ \alg -> runProg p alg >>= (\a -> runProg (k a) alg)

-- | Weaken a program of type @Prog effs a@ so that it can be used in
-- place of a program of type @Prog effs a@, when every @effs@ is a member of @effs'@.
weakenProg :: forall effs effs' a
  . ( Injects effs effs'
    , HFunctor (Effs effs)
    )
  => Prog effs a -> Prog effs' a
weakenProg p = Prog $ \alg -> runProg p (alg . injs)

-- | Evaluate a program using the supplied algebra. This is the
-- universal property from initial monad @Prog sig a@ equipped with
-- the algebra @Eff effs m -> m@.
{-# INLINE eval #-}
eval
  :: forall effs m a . (Monad m, HFunctor (Effs effs))
  => Algebra effs m
  -> Prog effs a -> m a
eval alg p = runProg p alg