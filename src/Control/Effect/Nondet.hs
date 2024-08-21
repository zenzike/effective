{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Nondet
  ( module Control.Effect.Nondet
  , Choose
  , Empty
  ) where

import Prelude hiding (or)

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped
import Control.Effect.Alternative

import Control.Monad.Trans.List

stop :: Members '[Empty] sig => Prog sig a
stop  = call (Alg Empty return)

or :: Members '[Choose] sig => Prog sig a -> Prog sig a -> Prog sig a
or x y = call (Scp (Choose x y) return)

{-# INLINE stop #-}
stop' :: Syntax t Empty effs => t Identity s
stop' = mcall (Alg Empty id)

select :: Members [Choose, Empty] sig => [a] -> Prog sig a
select = foldr (or . return) stop

selects :: [a] -> Progs [Choose, Empty] (a, [a])
selects []      =  empty
selects (x:xs)  =  return (x, xs)  <|>  do  (y, ys) <- selects xs
                                            return (y, x:ys)

nondet :: Handler [Empty, Choose] '[] (ListT) []
nondet = handler runListT' alternativeAlg

-- This does not work becuase `Choose` is algebraic, for a greedy approach
-- it must favour the lhs, but `return x <|> return y` prevents this
-- greedy :: Handler [Empty, Choose] '[] MaybeT '[Maybe]
-- greedy = handler runMaybeT alternativeAlg

-------------------------------
-- Example: Backtracking (and Culling?)
type Once = Scp Once'
data Once' a where
  Once :: a -> Once' a
  deriving Functor

once
  :: Member Once sig => Prog sig a -> Prog sig a
once p = call (Scp (Once p) return)

-- Everything can be handled together. Here is the non-modular way
-- list :: (Member (Choose) sig, Member (Empty) sig, Member (Once) sig) => Prog sig a -> [a]
list :: Prog [Empty, Choose, Once] a -> [a]
list = eval halg where
  halg :: Effs [Empty, Choose, Once] [] a -> [a]
  halg op
    | Just (Alg Empty k)          <- prj op = []
    | Just (Scp (Choose xs ys) k) <- prj op = fmap k (xs ++ ys)
    | Just (Scp (Once xs) k)      <- prj op = case xs of
                                                  []     -> []
                                                  (x:xs) -> [k x]

backtrackAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> (forall x. Effs [Empty, Choose, Once] (ListT m) x -> ListT m x)
backtrackAlg oalg op
  | Just (Alg Empty k)            <- prj op = empty
  | Just (Scp (Choose xs ys) k)   <- prj op = fmap k (xs <|> ys)
  | Just (Scp (Once p) k)         <- prj op =
    ListT $ do mx <- runListT (fmap k p)
               case mx of
                 Nothing       -> return Nothing
                 Just (x, mxs) -> return (Just (x, empty))

backtrackOnceAlg
  :: Monad m
  => (forall x . oeff m x -> m x)
  -> (forall x . Effs '[Once] (ListT m) x -> ListT m x)
backtrackOnceAlg oalg op
  | Just (Scp (Once p) k) <- prj op =
    ListT $ do mx <- runListT (fmap k p)
               case mx of
                 Nothing       -> return Nothing
                 Just (x, mxs) -> return (Just (x, empty))

backtrackAlg'
  :: Monad m => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs [Empty, Choose, Once] (ListT m) x -> ListT m x)
backtrackAlg' oalg = alternativeAlg oalg # backtrackOnceAlg oalg

backtrack :: Handler [Empty, Choose, Once] '[] (ListT) []
backtrack = handler runListT' backtrackAlg'

instance MAlgebra (ListT) where
  type IEffs (ListT) = '[Empty, Choose]
  type OEffs (ListT) = '[]

  {-# INLINE malg #-}
  malg = halg nondet