{-|
Module      : Control.Effect.CodeGen.Type
Description : Types for the code-generation effect
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains some basic definitions for type `Up` of code.
-}
{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Type where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Effect.State ( get, put, Get, Put )
import Control.Effect.Reader
import Control.Effect.Except
import Control.Effect ( Member, Prog )

-- | In two-level type theory, the type constructor @Up@ turns every object-level
-- type into a meta-level type. In Template Haskell, the object-level language 
-- and the meta-level language are the same.
type Up = CodeQ

-- | Print a piece of code.
printUp :: Up a -> IO ()
printUp a = do
  x <- unType <$> runQ (examineCode a)
  print $ ppr x

-- | In Andras Kovacs's original paper, intensional pattern matching on code
-- is not allowed, but it is allowed in Template Haskell and can be used
-- for example to implement this @codeApp@ such that @codeApp xs [|| [] ||]@
-- equals @xs@ (rather than @[|| $$xs ++ [] ||]@). We don't essentially rely on 
-- this but it is handy in a few places for generating better-looking code.
codeApp :: Up [a] -> Up [a] -> Up [a]
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

-- * Operations specialised for `Up`. 
--
-- Sometimes GHC has a hard time of inferring the type of operations like
-- @put [|| ... ||]@ because the quotation by default has type @Code m@.
-- So having some specialised operations is sometimes handy.

putUp :: Member (Put (Up c)) sig => Up c -> Prog sig ()
putUp = put

getUp :: Member (Get (Up c)) sig => Prog sig (Up c)
getUp = get

askUp :: Member (Ask (Up c)) sig => Prog sig (Up c)
askUp = ask 

localUp :: Member (Local (Up c)) sig => (Up c -> Up c) -> Prog sig (Up c) -> Prog sig (Up c)
localUp = local

throwUp :: Member (Throw (Up c)) sig => Up c -> Prog sig a 
throwUp = throw

catchUp :: Member (Catch (Up c)) sig => Prog sig a -> (Up c -> Prog sig a) -> Prog sig a 
catchUp = catch