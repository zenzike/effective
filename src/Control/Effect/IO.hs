{-# LANGUAGE DataKinds #-}

module Control.Effect.IO where

import Control.Effect
import Data.List.Kind
import Data.Functor.Composes
import Data.HFunctor

import Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.Reader as R
import Control.Monad.Trans.Class

import Control.Effect.Writer

data GetLine k  = GetLine (String -> k) deriving Functor

getLine :: Members '[GetLine] sig => Prog sig String
getLine = injCall (Alg (GetLine return))


data PutStrLn k = PutStrLn String k     deriving Functor

putStrLn :: Members '[PutStrLn] sig => String -> Prog sig ()
putStrLn str = injCall (Alg (PutStrLn str (return ())))


algIO :: Effs [GetLine, PutStrLn] IO a -> IO a
algIO eff
  | Just (Alg (GetLine k))    <- prj eff =
      do str <- Prelude.getLine
         return (k str)
  | Just (Alg (PutStrLn str k)) <- prj eff =
      do Prelude.putStrLn str
         return k

algPutStrLn :: Effs '[PutStrLn] IO a -> IO a
algPutStrLn eff
  | Just (Alg (PutStrLn str k)) <- prj eff =
      do Prelude.putStrLn str
         return k

evalIO :: Prog [GetLine, PutStrLn] a -> IO a
evalIO = eval algIO

handleIO
  :: forall ieffs oeffs fs a xeffs
  . ( Append ieffs (xeffs :\\ ieffs)
    , Injects oeffs xeffs
    , Injects (xeffs :\\ ieffs) xeffs
    , Recompose fs
    , xeffs ~ '[GetLine, PutStrLn] )
  => Handler ieffs oeffs fs
  -> Prog (ieffs `Union` xeffs) a -> IO (Composes fs a)
handleIO = handleWith algIO

-- -- Now if we want to be sensitive to `putStrLn`, and censor that output
-- -- under a `censor` operation, we must define a new handler.
-- censorPutStrLn' :: Handler '[PutStrLn, Censor String] '[PutStrLn] '[]
-- censorPutStrLn' = Handler $ Handler' run alg fwd where
--   run :: Monad m
--       => (forall x. Effs '[PutStrLn] m x -> m x)
--       -> (forall x. ReaderT (String -> String) m x -> m (Comps '[] x))
--   run oalg (ReaderT x) = fmap CNil (x id)
--   -- run oalg = fmap CNil . ($ False) . runReaderT
-- 
--   alg :: Monad m
--       => (forall x. Effs '[PutStrLn] m x -> m x)
--       -> (forall x. Effs [PutStrLn, Censor String] (ReaderT (String -> String) m) x -> ReaderT (String -> String) m x)
--   alg oalg eff
--     | Just (Alg (PutStrLn xs k)) <- prj eff =
--         do cipher <- ask
--            lift (oalg (Eff (Alg (PutStrLn (cipher xs) k))))
--     | Just (Scp (Censor f k)) <- prj eff =
--         do R.local ((f .)) k
-- 
--   fwd :: Monad m
--       => (forall x. Effs sig m x -> m x)
--       -> (forall x. Effs sig (ReaderT (String -> String) m) x -> ReaderT (String -> String) m x)
--   fwd oalg c = ReaderT (\f -> oalg $ hmap (flip runReaderT f) c)
-- 
-- -- Now if we want to be sensitive to `putStrLn`, and censor that output
-- -- under a `censor` operation, we must define a new handler.
-- censorPutStrLn'' :: Handler '[PutStrLn, Censor [String]] '[PutStrLn] '[]
-- censorPutStrLn'' = Handler $ Handler' run alg fwd where
--   run :: Monad m
--       => (forall x. Effs '[PutStrLn] m x -> m x)
--       -> (forall x. ReaderT ([String] -> [String]) m x -> m (Comps '[] x))
--   run oalg (ReaderT x) = fmap CNil (x id)
--   -- run oalg = fmap CNil . ($ False) . runReaderT
-- 
--   alg :: Monad m
--       => (forall x. Effs '[PutStrLn] m x -> m x)
--       -> (forall x. Effs [PutStrLn, Censor [String]] (ReaderT ([String] -> [String]) m) x -> ReaderT ([String] -> [String]) m x)
--   alg oalg eff
--     | Just (Alg (PutStrLn xs k)) <- prj eff =
--         do cipher <- ask
--            lift (oalg (Eff (Alg (PutStrLn (unlines (cipher [xs])) k))))
--     | Just (Scp (Censor f k)) <- prj eff =
--         do R.local ((f .)) k
-- 
--   fwd :: Monad m
--       => (forall x. Effs sig m x -> m x)
--       -> (forall x. Effs sig (ReaderT ([String] -> [String]) m) x -> ReaderT ([String] -> [String]) m x)
--   fwd oalg c = ReaderT (\f -> oalg $ hmap (flip runReaderT f) c)
-- 
-- -- Now if we want to be sensitive to `putStrLn`, and censor that output
-- -- under a `censor` operation, we must define a new handler.
-- censorPutStrLn''' :: ([String] -> [String]) -> Handler '[PutStrLn, Censor [String]] '[PutStrLn, Censor [String]] '[]
-- censorPutStrLn''' cipher = Handler $ Handler' run alg fwd where
--   run :: Monad m
--       => (forall x. Effs '[PutStrLn, Censor [String]] m x -> m x)
--       -> (forall x. ReaderT ([String] -> [String]) m x -> m (Comps '[] x))
--   run oalg (ReaderT mx) = fmap CNil (mx cipher)
-- 
--   alg :: Monad m
--       => (forall x. Effs '[PutStrLn, Censor [String]] m x -> m x)
--       -> (forall x. Effs [PutStrLn, Censor [String]] (ReaderT ([String] -> [String]) m) x -> ReaderT ([String] -> [String]) m x)
--   alg oalg eff
--     | Just (Alg (PutStrLn xs k)) <- prj eff =
--         do cipher <- ask
--            lift (oalg (Eff (Alg (PutStrLn (unlines (cipher [xs])) k))))
--     | Just (Scp (Censor f k)) <- prj eff =
--         ReaderT (\f' -> oalg (Effs (Eff (Scp (Censor f (runReaderT k (f' . f)))))))
-- 
--   fwd :: Monad m
--       => (forall x. Effs sig m x -> m x)
--       -> (forall x. Effs sig (ReaderT ([String] -> [String]) m) x -> ReaderT ([String] -> [String]) m x)
--   fwd oalg c = ReaderT (\f -> oalg $ hmap (flip runReaderT f) c)
-- 
