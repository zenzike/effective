{-# LANGUAGE DataKinds #-}

module Control.Effect.IO where

import Control.Effects
import Control.Handler
import Control.Family.AlgScp
import Data.List.Kind
import Data.Functor.Composes

data GetLine' k  = GetLine (String -> k) deriving Functor

type GetLine = Algebraic GetLine'

getLine :: Members '[GetLine] sig => Prog sig String
getLine = injCall (Algebraic (GetLine return))


data PutStrLn' k = PutStrLn String k     deriving Functor

type PutStrLn = Algebraic PutStrLn'

putStrLn :: Members '[PutStrLn] sig => String -> Prog sig ()
putStrLn str = injCall (Algebraic (PutStrLn str (return ())))


algIO :: Effs [GetLine, PutStrLn] IO a -> IO a
algIO eff
  | Just (Algebraic (GetLine k))    <- prj eff =
      do str <- Prelude.getLine
         return (k str)
  | Just (Algebraic (PutStrLn str k)) <- prj eff =
      do Prelude.putStrLn str
         return k

algPutStrLn :: Effs '[PutStrLn] IO a -> IO a
algPutStrLn eff
  | Just (Algebraic (PutStrLn str k)) <- prj eff =
      do Prelude.putStrLn str
         return k

evalIO :: Prog [GetLine, PutStrLn] a -> IO a
evalIO = eval algIO

handleIO
  :: forall ieffs oeffs fs a xeffs fam
  . ( Append ieffs (xeffs :\\ ieffs)
    , Injects oeffs xeffs
    , Injects (xeffs :\\ ieffs) xeffs
    , Recompose fs
    , fam (Effs '[GetLine, PutStrLn])
    , xeffs ~ '[GetLine, PutStrLn] )
  => Handler ieffs oeffs fs fam
  -> Prog (ieffs `Union` xeffs) a -> IO (Composes fs a)
handleIO = handleWith algIO


instance ShowAlgOp GetLine' where
  showAlgOperator _ = "GetLine"
  showAlgOperands (GetLine k) = "xyz |-> " ++ show (k "xyz")

instance ShowAlgOp PutStrLn' where
  showAlgOperator (PutStrLn str _) = "PutStrLn " ++ str
  showAlgOperands (PutStrLn _ x) = show x
