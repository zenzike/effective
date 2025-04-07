module Control.Monad.Trans.CRes (
  module Control.Monad.Trans.CRes,
  module Control.Monad.Trans.Resump
  ) where

import Control.Monad.Trans.Resump
import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad
import Control.Effect.Concurrency.Action
import Data.List (nub)

-- Step functor for choice and action
data CStep a x = FailS | ChoiceS x x | ActS a x deriving Functor

-- The monad `CResT m` is the coproduct of the monad `m` and the 
-- free monad over CStep. In other words, the algebraic theory
-- corresponding to `CResT m` is the sum of the theory of `m`
-- plus a nullary operation, a binary operation, and a unary operation
-- for each action.
type CResT a = ResT (CStep a)

newtype ListActs a x = ListActs { unListActs :: [([a], x)] } deriving (Show, Functor)

-- Traverse all nondeterministic branches and accumulate the `m`-effects
-- and actions.
-- TODO: the manipulation of the lists can be more efficient.
runAll :: Monad m => CResT a m x -> m (ListActs a x)
runAll = fmap ListActs . runAll' [] where
  runAll' :: Monad m => [a] -> CResT a m x -> m [([a], x)]
  runAll' as (ResT m) = do x <- m
                           case x of
                             Left x -> return [(reverse as, x)]
                             Right (ActS a m') -> runAll' (a:as) m'
                             Right FailS -> return []
                             Right (ChoiceS ml mr) -> 
                               do l <- runAll' as ml
                                  r <- runAll' as mr
                                  return (l ++ r)

-- A specialised version of runAll' that prints more debug information
runAllIO :: (Eq a, Eq x, Show x, Show a) => CResT a IO x -> IO [([a], x)]
runAllIO = fmap nub . runAll' "" [] where
  runAll' :: (Show x, Show a) => String -> [a] -> CResT a IO x -> IO [([a], x)]
  runAll' indent as (ResT m) =
     do x <- m
        case x of
          Left x ->
             let ok = (reverse as, x) 
             in do putStr indent; print ok; return [ok]
          Right (ActS a m') -> runAll' indent (a:as) m'
          Right FailS -> 
            do putStrLn (indent ++ "Failed, backtracking")
               return []
          Right (ChoiceS ml mr) ->
            do putStrLn (indent ++ "Trying left")
               l <- runAll' (indent ++ "  ") as ml
               putStrLn (indent ++ "Trying right")
               r <- runAll' (indent ++ "  ") as mr
               putStrLn (indent ++ "Backtracking")
               return (l ++ r)

newtype ActsMb a x = ActsMb { unActsMb :: ([a], Maybe x) } deriving (Functor, Show)

-- Resolving the nondeterministic choices with the given Booleans.
runWith :: Monad m => [Bool] -> CResT a m x -> m (ActsMb a x)
runWith = runWith' [] where
  runWith' :: Monad m => [a] -> [Bool] -> CResT a m x -> m (ActsMb a x)
  runWith' as bs (ResT m) = 
    do xs <- m
       case xs of 
         Left x      -> return (ActsMb (reverse as, Just x))
         Right FailS -> return (ActsMb (reverse as, Nothing))
         Right (ChoiceS l r) ->
            let (b:bs') = bs 
            in runWith' as bs' (if b then l else r)
         Right (ActS a m) -> runWith' (a:as) bs m

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

(<|>:) :: Monad m => CResT a m x -> CResT a m x -> m (Either x (CStep a (CResT a m x)))
x <|>: y = unResT (x <|> y)

prefix :: Monad m => a -> CResT a m x -> CResT a m x
prefix a m = ResT $ prefix' a m

prefix' :: Monad m => a -> CResT a m x -> m (Either x (CStep a (CResT a m x)))
prefix' a m = return (Right (ActS a m))

fail :: Monad m => CResT a m x
fail = ResT fail'

fail' :: Monad m => m (Either x (CStep a (CResT a m x)))
fail' = return (Right FailS)

done' :: Monad m => a -> m (Either a b)
done' x = return (Left x)

-- parallel composition of processes (only the left argument's return
-- value is kept in the combined process.)
par :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
par x y = (parL x y <|> parR x y) <|> (parCL x y <|> parCR x y)

-- parallel composition, and the left argument acts first
parL :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
parL (ResT mxs) y = ResT $
  do xs <- mxs
     case xs of
       Left x -> unResT $ fmap (const x) y
       Right (ActS a m)    -> prefix' a (par m y)
       Right FailS         -> fail'
       Right (ChoiceS l r) -> parL l y <|>: parL r y

-- parallel composition, and the right argument acts first
parR :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
parR x (ResT mys) = ResT $
  do ys <- mys
     case ys of
       Left y -> unResT $ x
       Right (ActS a m)    -> prefix' a (par x m)
       Right FailS         -> fail'
       Right (ChoiceS l r) -> parR x l <|>: parR x r

-- parallel composition, and the two arguments interact first, and the 
-- `m`-effect of left argument is run first
parCL :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
parCL lhs rhs = ResT $
  do xs <- unResT lhs
     case xs of 
       Left x -> fail'
       Right (ActS a m) -> 
         do ys <- unResT rhs
            case ys of
              Right (ActS b n) -> 
                case merge a b of
                  Nothing -> fail'
                  Just c -> prefix' c (par m n)
              Right (ChoiceS l' r') -> 
                (parCR (prefix a m) l') <|>: (parCR (prefix a m) r')
              _ -> fail'
       Right FailS -> fail'
       Right (ChoiceS l r) -> parCL l rhs <|>: parCL r rhs

-- parallel composition, and the two arguments interact first, and the 
-- `m`-effect of right argument is run first
parCR :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
parCR lhs rhs = ResT $
  do ys <- unResT rhs
     case ys of 
       Left y -> fail'
       Right (ActS a m) -> 
         do xs <- unResT lhs
            case xs of
              Right (ActS b n) -> 
                case merge b a of
                  Nothing -> fail'
                  Just c -> prefix' c (par n m)
              Right (ChoiceS l' r') -> 
                parCL l' (prefix a m) <|>: parCL r' (prefix a m)
              _ -> fail'
       Right FailS -> fail'
       Right (ChoiceS l r) -> parCR lhs l <|>: parCR lhs r

res :: (Action a, Monad m) => a -> CResT a m x -> CResT a m x
res a p = ResT $
  do xs <- unResT p
     case xs of
       Left x -> done' x
       Right (ActS b m) ->
         if a == b then fail' else prefix' b (res a m)
       Right (ChoiceS l r) -> res a l <|>: res a r
       Right FailS -> fail'