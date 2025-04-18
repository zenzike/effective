{-# LANGUAGE TemplateHaskell #-}
module Control.Effect.CodeGen.Type where

import Language.Haskell.TH

type Up = CodeQ

printUp :: Up a -> IO ()
printUp a = do
  x <- unType <$> runQ (examineCode a)
  print $ ppr x