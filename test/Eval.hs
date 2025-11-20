{-# LANGUAGE PatternSynonyms, ViewPatterns, LambdaCase, TemplateHaskell #-}
module Main where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Maybe
import Control.Monad.Trans.Cont
import Data.Functor.Identity

$(makeGen [e| var :: String -> Int |])

{-
type Var = Alg Var_

var :: Member Var sig => String -> Prog sig a
var name = call (Alg (Var_ name))

pattern Var :: Member Var effs => String -> Effs effs m k
pattern Var name <- (prj -> Just (Alg (Var_ name)))
  where Var name = inj (Alg (Var_ name))
-}

data Add_ k = Add_ k k
  deriving Functor

type Add = Alg Add_

add :: Member Add sig => Prog sig a -> Prog sig a -> Prog sig a
add x y = callJ (Alg (Add_ x y))

pattern Add :: Member Add effs => k -> k -> Effs effs m k
pattern Add x y <- (prj -> Just (Alg (Add_ x y)))
  where Add x y = inj (Alg (Add_ x y))

exprAT :: [(String, Int)] -> AlgTrans '[Var, Add] '[Throw] '[ContT Int] Monad
exprAT env = AlgTrans $ \oalg op ->
  case op of
    Var str k -> case lookup str env of
      Nothing -> ContT $ \k -> callM oalg (Alg Throw_)
      Just v  -> return (k v)
    Add x y  -> ContT $ \k -> do x' <- k x; y' <- k y; return (x' + y')

expr :: [(String, Int)] -> Handler '[Var, Add] '[Throw] '[ContT Int] Int Int
expr choices = exprAT choices #: runner (\t -> runContT t return)

evalExpr :: Prog [Var, Add] Int -> Maybe Int
evalExpr p = runIdentity . runMaybeT . flip runContT return $
  evalAT' (exprAT [("x", 3)] `pipeAT` exceptAT) p

h :: [(String, Int)] -> Handler '[Var, Add] '[] [ContT Int, MaybeT] Int (Maybe Int)
h env = expr env ||> except

-- evalExpr' :: [(String, Int)] -> Progs [Var, Add, Catch] Int -> Maybe Int
-- evalExpr' env p = handle (expr env |> except) p

-- >>> :t runIdentity . runMaybeT . flip runContT return
-- runIdentity . runMaybeT . flip runContT return :: ContT a (MaybeT Identity) a -> Maybe a

-- >>> :t 4 @Int
-- Cannot apply expression of type `a0_auhC[tau:1]'
-- to a visible type argument `Int'
-- In the expression: 4 @Int

ex :: Prog '[Var, Add] Int
ex = add (add (pure 1) (pure 2)) (var "x")

ex2 :: Prog '[Var, Add] Int
ex2 = add (add (pure 1) (pure 2)) (var "y")

-- >>> test1
-- Just 6
test1 :: Maybe Int
test1 = evalExpr ex

-- >>> test2
-- Nothing
test2 :: Maybe Int
test2 = evalExpr ex2

-- >>> test3
-- Just 6
test3 :: Maybe Int
test3 = handle (h [("x", 3)]) ex

main :: IO()
main = return ()
