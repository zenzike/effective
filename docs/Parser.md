```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}

module Parser where

import Control.Effect
import Control.Effect.Cut
import Control.Effect.Nondet
import Control.Effect.State

import Hedgehog

import Prelude hiding (or)

import Control.Applicative

char :: Char ! [Get [Char], Put [Char], Empty, Choose]
char = do
  xxs <- get
  case xxs of
    []     -> empty
    (x:xs) -> do put xs
                 return x

symbol :: Members [Get [Char], Put [Char], Empty, Choose] sig => Char -> Prog sig Char
symbol c = do
  c' <- char
  if c == c'
    then return c
    else empty

digit :: Members [Get [Char], Put [Char], Empty, Choose] sig => Prog sig Char
digit = foldr (<|>) empty (fmap symbol ['0' .. '9'])

int, expr, term, fact :: Members [Get [Char], Put [Char], Empty, Choose] sig => Prog sig Int
int  = do ds <- some digit ; return (read ds)
expr = (do i <- term ; symbol '+' ; j <- expr ; return (i + j))
   <|> (do i <- term ; return i)
term = (do i <- fact ; symbol '*' ; j <- term ; return (i * j))
   <|> (do i <- fact ; return i)
fact = (int)
   <|> (do symbol '(' ; i <- expr ; symbol ')' ; return i)

-- int', expr', term', fact' :: forall sig .
--   ( Member ((Get [Char])) sig
--   , Member ((Put [Char])) sig
--   , Member (Empty) sig
--   , Member (Choose) sig)
--   => Prog sig Int
--
-- int'  = read <$> some digit
-- expr' = ((+) <$> term' <* symbol '+' <*> expr') <|> term'
-- term' = ((*) <$> fact' <* symbol '*' <*> term') <|> fact'
-- fact' = int <|> (symbol '(' *> expr' <* symbol ')')
--

-- A parser!
parse
  :: text -> a ! [Put text, Get text, Empty, Choose]
  -> [(text, a)]
parse cs p = handle (state cs `fuse` list) p

parseBacktrack
  :: text -> a ! [Put text, Get text, Empty, Choose, Once]
  -> [(text, a)]
parseBacktrack cs p = handle (unscope (Proxy @(Choose_)) |> state cs |> backtrack) p

example_Parse1 :: Property
example_Parse1 = property $
    (parse "2+3*5" expr :: [(String, Int)])
  ===
    [("",17),("*5",5),("+3*5",2)]

-- Not a parser!
notParse
  :: String -> Prog [Empty, Choose, Put String, Get String] a
  -> (String, [a])
notParse cs p = handle (hide (Proxy @'[Once]) list |> state cs) p

example_NotParse :: Property
example_NotParse = property $
    (notParse "2+3*5" expr :: (String, [Int]))
  ===
    ("",[])

-- This example demonstrates the use of Cut
expr', term', fact' :: forall sig .
  Members [Get [Char], Put [Char], Empty, Choose, CutFail, CutCall] sig
  => Prog sig Int
expr' = do i <- term'
           cutCall ((do symbol '+' ; cut; j <- expr' ; return (i + j)) <|>
                    (do return i))
term' = do i <- fact'
           cutCall ((do symbol '*' ; cut; j <- term' ; return (i * j)) <|>
                    (do return i))
fact' = int <|> (do symbol '(' ; i <- expr' ; symbol ')' ; return i)
--
-- A different parser!
parse' :: text -> Prog [Put text, Get text, Once, Empty, Choose, CutFail, CutCall] a -> [(text, a)]
parse' cs p  = handle (state cs `fuse` onceNondet) p

example_Parse2 :: Property
example_Parse2 = property $
    (parse' "2+3*5" expr' :: [(String, Int)])
  ===
    [("",17)]

examples :: Group
examples = $$(discoverPrefix "example_")
```haskell
