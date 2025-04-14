module Control.Monad.Trans.CRes (
  module Control.Monad.Trans.CRes,
  module Control.Monad.Trans.Resump
  ) where

import Control.Monad.Trans.Resump
import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad
import Control.Effect.Concurrency.Types (Action (..))
import Data.List (nub)

-- | Step functor for choice and action
data CStep a x = FailS | ChoiceS x x | ActS a x deriving Functor

-- | The monad `CResT m` is the coproduct of the monad `m` and the 
-- free monad over CStep. In other words, the algebraic theory
-- corresponding to `CResT m` is the sum of the theory of `m`
-- plus a nullary operation, a binary operation, and a unary operation
-- for each action.
type CResT a = ResT (CStep a)

-- | The functor type for the results of running a nondeterministic process by backtracking.
newtype ListActs a x = ListActs { unListActs :: [([a], x)] } deriving (Show, Functor)

-- | Traverse all nondeterministic branches and accumulate the `m`-effects
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

-- | A specialised version of runAll' that prints some debug information
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

-- | The functor type for the results of running a nondeterministic process by a given
-- list of Booleans for resolving choices.
newtype ActsMb a x = ActsMb { unActsMb :: ([a], Maybe x) } deriving (Functor, Show)

-- | Run a nondeterministic process, using the given Booleans to resolve the choices.
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


-- | Run a nondeterministic process, using the given Boolean-producing
-- monadic action to resolve the choices.
runWithM :: forall a m x. Monad m => m Bool -> CResT a m x -> m (ActsMb a x)
runWithM mb = runWithM' [] where
  runWithM' :: [a] -> CResT a m x -> m (ActsMb a x)
  runWithM' as (ResT m) = 
    do xs <- m
       case xs of 
         Left x      -> return (ActsMb (reverse as, Just x))
         Right FailS -> return (ActsMb (reverse as, Nothing))
         Right (ChoiceS l r) ->
            do b <- mb
               runWithM' as (if b then l else r)
         Right (ActS a m) -> runWithM' (a:as) m

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

-- | Joined parallel composition of processes. The process @jpar x y@ interleaves
-- the actions of @x@ and @y@ in all possible ways nondeterministically.
jpar :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m (x, y)
jpar x y = (jparL x y <|> jparR x y) <|> (jparCL x y <|> jparCR x y)

-- | Joined parallel composition with the left argument acts first.
jparL :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m (x, y)
jparL (ResT mxs) y = ResT $
  do xs <- mxs
     case xs of
       Left x -> unResT $ fmap ((x,)) y
       Right (ActS a m)    -> prefix' a (jpar m y)
       Right FailS         -> fail'
       Right (ChoiceS l r) -> jparL l y <|>: jparL r y

-- | Joined parallel composition with the right argument acts first.
jparR :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m (x, y)
jparR x y = fmap (\(a,b) -> (b,a)) (jparL y x)

-- | Joined parallel composition with the two arguments communicate first, but
-- the monadic effect of the left argument is executed first.
jparCL :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m (x, y)
jparCL lhs rhs = ResT $
  do xs <- unResT lhs
     case xs of 
       Left x -> fail'
       Right (ActS a m) -> 
         do ys <- unResT rhs
            case ys of
              Right (ActS b n) -> 
                case merge a b of
                  Nothing -> fail'
                  Just c -> prefix' c (jpar m n)
              Right (ChoiceS l' r') -> 
                jparCR (prefix a m) l' <|>: (jparCR (prefix a m) r')
              _ -> fail'
       Right FailS -> fail'
       Right (ChoiceS l r) -> jparCL l rhs <|>: jparCL r rhs

-- | Joined parallel composition with the two arguments communicate first, but
-- the monadic effect of the right argument is executed first.
jparCR :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m (x, y)
jparCR lhs rhs = fmap (\(a,b) -> (b,a)) (jparCL rhs lhs)

-- | Parallel composition of processes (only the left argument's return
-- value is kept in the combined process.)
par :: (Action a, Monad m) => CResT a m x -> CResT a m y -> CResT a m x
par x y = fmap fst (jpar x y)

-- | The process @res a p@ acts like @p@ under a firewall that blocks all communication of
-- @p@ with the external environment via action @a@.
res :: (Action a, Monad m) => a -> CResT a m x -> CResT a m x
res a p = ResT $
  do xs <- unResT p
     case xs of
       Left x -> done' x
       Right (ActS b m) ->
         if a == b then fail' else prefix' b (res a m)
       Right (ChoiceS l r) -> res a l <|>: res a r
       Right FailS -> fail'