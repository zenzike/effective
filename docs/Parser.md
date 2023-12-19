```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}

module Parser where

import Hedgehog

import Prelude hiding (or)

import Control.Applicative

import Control.Effects
import Control.Handler
import Control.Effect.Cut
import Control.Effect.Nondet
import Control.Effect.State

char :: Prog' '[Get [Char], Put [Char], Stop, Or] Char
char = do
  xxs <- get
  case xxs of
    []     -> stop
    (x:xs) -> do put xs
                 return x

symbol :: Members [Get [Char], Put [Char], Stop, Or] sig => Char -> Prog sig Char
symbol c = do
  c' <- char
  if c == c'
    then return c
    else stop

digit :: Members [Get [Char], Put [Char], Stop, Or] sig => Prog sig Char
digit = foldr (<|>) stop (fmap symbol ['0' .. '9'])

int, expr, term, fact :: Members [Get [Char], Put [Char], Stop, Or] sig => Prog sig Int
int  = do ds <- some digit ; return (read ds)
expr = or (do i <- term ; symbol '+' ; j <- expr ; return (i + j))
          (do i <- term ; return i)
term = or (do i <- fact ; symbol '*' ; j <- term ; return (i * j))
          (do i <- fact ; return i)
fact = or (int)
          (do symbol '(' ; i <- expr ; symbol ')' ; return i)

-- int', expr', term', fact' :: forall sig .
--   ( Member ((Get [Char])) sig
--   , Member ((Put [Char])) sig
--   , Member (Stop) sig
--   , Member (Or) sig)
--   => Prog sig Int
--
-- int'  = read <$> some digit
-- expr' = ((+) <$> term' <* symbol '+' <*> expr') <|> term'
-- term' = ((*) <$> fact' <* symbol '*' <*> term') <|> fact'
-- fact' = int <|> (symbol '(' *> expr' <* symbol ')')
--

-- A parser!
parse
  :: text -> Prog [Put text, Get text, Stop, Or] a
  -> [(text, a)]
parse cs p = handle (state cs <&> nondet) p

example_Parse1 :: Property
example_Parse1 = property $
    (parse "2+3*5" expr :: [(String, Int)])
  ===
    [("",17),("*5",5),("+3*5",2)]

-- Not a parser!
notParse
  :: String -> Prog [Stop, Or, Put String, Get String] a
  -> (String, [a])
notParse cs p = handle (nondet <&> state cs) p

example_NotParse :: Property
example_NotParse = property $
    (notParse "2+3*5" expr :: (String, [Int]))
  ===
    ("",[])

-- This example demonstrates the use of Cut
expr', term', fact' :: forall sig .
  Members [Get [Char], Put [Char], Stop, Or, CutFail, CutCall] sig
  => Prog sig Int
expr' = do i <- term'
           cutCall (or (do symbol '+' ; cut; j <- expr' ; return (i + j))
                       (do return i))
term' = do i <- fact'
           cutCall (or (do symbol '*' ; cut; j <- term' ; return (i * j))
                       (do return i))
fact' = or int
           (do symbol '(' ; i <- expr' ; symbol ')' ; return i)
--
-- A different parser!
parse' :: text -> Prog [Put text, Get text, Once, Stop, Or, CutFail, CutCall] a -> [(text, a)]
parse' cs p  = handle (state cs <&> onceNondet) p

example_Parse2 :: Property
example_Parse2 = property $
    (parse' "2+3*5" expr' :: [(String, Int)])
  === 
    [("",17)]

examples :: Group
examples = $$(discoverPrefix "example_")
```haskell
