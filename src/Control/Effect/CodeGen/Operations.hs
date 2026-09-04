{-|
Module      : Control.Effect.CodeGen.Operations
Description : Types for the code-generation effect
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains some basic definitions for type `CodeQ` of code.
-}
{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Operations
  ( module Control.Effect.CodeGen.Operations
  , CodeQ (..)
  ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Effect.State ( get, put, Get, Put )
import Control.Effect.Reader
import Control.Effect.Except
import Control.Effect ( Member, Prog )

-- | Print a piece of code.
printCodeQ :: CodeQ a -> IO ()
printCodeQ a = do
  x <- unType <$> runQ (examineCode a)
  print $ ppr x

-- | In Andras Kovacs's original paper, intensional pattern matching on code
-- is not allowed, but it is allowed in Template Haskell and can be used
-- for example to implement this @codeApp@ such that @codeApp xs [|| [] ||]@
-- equals @xs@ (rather than @[|| $$xs ++ [] ||]@). We don't essentially rely on
-- this but it is handy in a few places for generating better-looking code.
codeApp :: CodeQ [a] -> CodeQ [a] -> CodeQ [a]
codeApp cql@(Code ql) cqr@(Code qr) = Code $
  do r <- qr
     if isEmptyListExp r
       then ql
       else examineCode [|| $$cql ++ $$cqr ||]
  where
    isEmptyListExp :: TExp [a] -> Bool
    isEmptyListExp (TExp (ConE e))
      | e == '[]     =  True
    isEmptyListExp _ = False

-- * Operations specialised for `CodeQ`.
--
-- Sometimes GHC has a hard time inferring the type of operations like
-- @put [|| ... ||]@ because the quotation by default has type @Code m@.
-- So having some specialised operations is sometimes handy.

putC :: Member (Put (CodeQ c)) effs => CodeQ c -> Prog effs ()
putC = put

getC :: Member (Get (CodeQ c)) effs => Prog effs (CodeQ c)
getC = get

askC :: Member (Ask (CodeQ c)) effs => Prog effs (CodeQ c)
askC = ask

localC :: Member (Local (CodeQ c)) effs => (CodeQ c -> CodeQ c) -> Prog effs (CodeQ c) -> Prog effs (CodeQ c)
localC = local

throwC :: Member (Throw (CodeQ c)) effs => CodeQ c -> Prog effs a
throwC = throw

catchC :: Member (Catch (CodeQ c)) effs => Prog effs a -> (CodeQ c -> Prog effs a) -> Prog effs a
catchC = catch
