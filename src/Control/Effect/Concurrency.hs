module Control.Effect.Concurrency where

import Control.Monad.Trans.Resump
import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad
import Data.Bifunctor ( Bifunctor(bimap) )
import GHC.CmmToAsm.AArch64.Instr (_d)

class Action a where
  merge :: a -> a -> Maybe a

-- Step functor for choice and action
data CStep a x = FailS | ChoiceS x x | ActS a x deriving Functor

-- The monad `CResT m` is the coproduct of the monad `m` and the 
-- free monad over CStep. In other words, the algebraic theory
-- corresponding to `CResT m` is the sum of the theory of `m`
-- plus a nullary operation, a binary operation, and a unary operation
-- for each action.
type CResT a = ResT (CStep a)

-- Traverse all nondeterministic branches and accumulate the `m`-effects
-- and actions.
runAll :: Monad m => CResT a m x -> m [([a], x)]
runAll = (fmap ($ [])) . runAll' where
  runAll' :: Monad m => CResT a m x -> m ([([a], x)] -> [([a], x)])
  runAll' (ResT m) = do x <- m
                        case x of
                          Left x -> return (([], x):)

                          Right (ActS a m') ->
                            fmap ((map (bimap (a:) id)) .) (runAll' m')

                          Right FailS -> return id

                          Right (ChoiceS ml mr) -> 
                            do l <- runAll' ml
                               r <- runAll' mr
                               return (l . r)

instance Monad m => Alternative (CResT a m) where
  {-# INLINE empty #-}
  empty :: Monad m => CResT a m x
  empty = ResT (return (Right FailS))

  {-# INLINE (<|>) #-}
  (<|>) :: Monad m => CResT a m x -> CResT a m x -> CResT a m x
  mxs <|> mys = ResT $ return (Right (ChoiceS mxs mys))

instance Monad m => MonadPlus (CResT a m) where
  {-# INLINE mzero #-}
  mzero = empty
  {-# INLINE mplus #-}
  mplus :: Monad m => CResT a m x -> CResT a m x -> CResT a m x
  mplus = (<|>)

prefix :: Monad m => a -> CResT a m x -> CResT a m x
prefix a m = ResT $ prefix' a m

prefix' :: Monad m => a -> CResT a m x -> m (Either x (CStep a (CResT a m x)))
prefix' a m = return (Right (ActS a m))

fail :: Monad m => CResT a m x
fail = ResT fail'

fail' :: Monad m => m (Either x (CStep a (CResT a m x)))
fail' = return (Right FailS)


-- parallel composition of processes (only the left argument's return
-- value is kept in the combined process.)
par :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
par x y = parL x y <|> parR x y <|> parCL x y <|> parCR x y

-- parallel composition, and the left argument acts first
parL :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
parL (ResT mxs) y = ResT $
  do xs <- mxs
     case xs of
       Left x -> unResT $ fmap (const x) y
       Right (ActS a m)    -> prefix' a (par m y)
       Right FailS         -> fail'
       Right (ChoiceS l r) -> unResT (parL l y <|> parL r y)

-- parallel composition, and the right argument acts first
parR :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
parR x (ResT mys) = ResT $
  do ys <- mys
     case ys of
       Left y -> unResT $ x
       Right (ActS a m)    -> prefix' a (par x m)
       Right FailS         -> fail'
       Right (ChoiceS l r) -> unResT (parR x l <|> parR x r)

-- parallel composition, and the two arguments interact first, and the 
-- `m`-effect of left argument is run first
parCL :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
parCL (ResT mxs) y@(ResT mys) = ResT $
  do xs <- mxs
     case xs of 
       Left x -> fail'
       Right (ActS a m) -> 
         do ys <- mys
            case ys of
              Right (ActS b n) -> 
                case merge a b of
                  Nothing -> fail'
                  Just c -> prefix' c (par m n)
              Right (ChoiceS l' r') -> 
                unResT (parCR (prefix a m) l' <|> parCR (prefix a m) r')
              _ -> fail'
       Right FailS -> fail'
       Right (ChoiceS l r) -> unResT (parCL l y <|> parCL r y)

-- parallel composition, and the two arguments interact first, and the 
-- `m`-effect of right argument is run first
parCR :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
parCR x@(ResT mxs) (ResT mys) = ResT $
  do ys <- mys
     case ys of 
       Left y -> fail'
       Right (ActS a m) -> 
         do xs <- mxs
            case xs of
              Right (ActS b n) -> 
                case merge b a of
                  Nothing -> fail'
                  Just c -> prefix' c (par n m)
              Right (ChoiceS l' r') -> 
                unResT (parCL l' (prefix a m) <|> parCL r' (prefix a m))
              _ -> fail'
       Right FailS -> fail'
       Right (ChoiceS l r) -> unResT (parCR x l <|> parCR x r)