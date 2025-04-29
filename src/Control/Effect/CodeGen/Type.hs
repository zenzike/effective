{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Type where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

type Up = CodeQ

printUp :: Up a -> IO ()
printUp a = do
  x <- unType <$> runQ (examineCode a)
  print $ ppr x

codeApp :: Up [a] -> Up [a] -> Up [a]
codeApp cql@(Code ql) cqr@(Code qr) = Code $ 
  do r <- qr
     if isEmptyListExp r 
       then ql 
       else examineCode [|| $$cql ++ $$cqr ||]

isEmptyListExp :: TExp [a] -> Bool 
isEmptyListExp (TExp (ConE e))
  | e == '[]     =  True
isEmptyListExp _ = False