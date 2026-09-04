```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}

module Parser where

import Control.Effect
import Control.Effect.Nondet.Cut
import Control.Effect.Nondet.List
import Control.Effect.Nondet.Alternative (chooseByNondet, list)
import Control.Effect.State

import Hedgehog

import Prelude hiding (or)

char :: Char ! [Get [Char], Put [Char], Empty, Choose]
char = do
  xxs <- get
  case xxs of
    []     -> empty
    (x:xs) -> do put xs
                 return x

symbol :: Members [Get [Char], Put [Char], Empty, Choose] effs => Char -> Prog effs Char
symbol c = do
  c' <- char
  if c == c'
    then return c
    else empty

digit :: Members [Get [Char], Put [Char], Empty, Choose] effs => Prog effs Char
digit = foldr (<|>) empty (fmap symbol ['0' .. '9'])

int, expr, term, fact :: Members [Get [Char], Put [Char], Empty, Choose] effs => Prog effs Int
int  = do ds <- some digit ; return (read ds)
expr = (do i <- term ; symbol '+' ; j <- expr ; return (i + j))
   <|> (do i <- term ; return i)
term = (do i <- fact ; symbol '*' ; j <- term ; return (i * j))
   <|> (do i <- fact ; return i)
fact = (int)
   <|> (do symbol '(' ; i <- expr ; symbol ')' ; return i)

-- int', expr', term', fact' :: forall effs .
--   ( Member ((Get [Char])) effs
--   , Member ((Put [Char])) effs
--   , Member (Empty) effs
--   , Member (Choose) effs)
--   => Prog effs Int
--
-- int'  = read <$> some digit
-- expr' = ((+) <$> term' <* symbol '+' <*> expr') <|> term'
-- term' = ((*) <$> fact' <* symbol '*' <*> term') <|> fact'
-- fact' = int <|> (symbol '(' *> expr' <* symbol ')')
--

-- A parser!
parse
  :: text -> a ! [Put text, Get text, Empty, Choose]
  -> [(a, text)]
parse cs p = handle (state cs `fuse` list) p

parseBacktrack
  :: text -> a ! [Put text, Get text, Empty, Choose, Once]
  -> [(a, text)]
parseBacktrack cs p = handle (chooseByNondet |> state cs |> backtrack) p

example_Parse1 :: Property
example_Parse1 = property $
    (parse "2+3*5" expr :: [(Int, String)])
  ===
    [(17,""),(5,"*5"),(2,"+3*5")]

-- Not a parser!
notParse
  :: String -> Prog [Empty, Choose, Put String, Get String] a
  -> ([a], String)
notParse cs p = handle (hide (Proxy @'[Once]) list |> state cs) p

example_NotParse :: Property
example_NotParse = property $
    (notParse "2+3*5" expr :: ([Int], String))
  ===
    ([],"")

-- This example demonstrates the use of Cut
expr', term', fact' :: forall effs .
  Members [Get [Char], Put [Char], Empty, Choose, CutFail, CutCall] effs
  => Prog effs Int
expr' = do i <- term'
           cutCall ((do symbol '+' ; cut; j <- expr' ; return (i + j)) <|>
                    (do return i))
term' = do i <- fact'
           cutCall ((do symbol '*' ; cut; j <- term' ; return (i * j)) <|>
                    (do return i))
fact' = int <|> (do symbol '(' ; i <- expr' ; symbol ')' ; return i)
--
-- A different parser!
parse' :: text -> Prog [Put text, Get text, Once, Empty, Choose, NondetOr, CutFail, CutCall] a -> [(a, text)]
parse' cs p  = handle (state cs `fuse` onceNondet) p

example_Parse2 :: Property
example_Parse2 = property $
    (parse' "2+3*5" expr' :: [(Int, String)])
  ===
    [(17,"")]

examples :: Group
examples = $$(discoverPrefix "example_")
```haskell
