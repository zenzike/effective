{-|
Module      : Control.Effect.CodeGen.Concurrency
Description : Algebra transformers for staging concurrency
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains algebra transformers for `ResUpT`, the monad transformer to be
used at the meta level for resumption. The monad transformer `ResUpT` can be downed 
to and upped from the (object-level) resumption monad transformer @ResT@.
Moreover, for every functor @s@, the monad `ResUpT s n` supports algebraic 
operations of signature @s@ the same way as @ResT s@.

However, we also have operations on @ResT s m@ that are defined by pattern matching
and recursion, such as @parL@ in "Control.Monad.Trans.CResT". These operations can't
be implemented on @ResUpT@ because @ResUpT@ doesn't support pattern matching.

An imperfect workaround is to have /restricted version/ of these operations at the meta
level, such as @`parUp` :: m (Up x) -> m (Up x) -> m (Up x)@ where the return value 
must be code, and `ResUpT` supports operations like this by downing 
the arguments to the object level and invoke the object-level algebra, and then up
the result back to the meta level. This is of course very unsatisfactory but currently
I don't know how to do better.
-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances, BlockArguments, MonoLocalBinds, ViewPatterns #-}
module Control.Effect.CodeGen.Concurrency where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Down
import Control.Effect.Yield
import Control.Effect.Concurrency.Type (Action (..), Act (..), Act_(..))
import Control.Effect.Nondet

import Control.Monad.Trans.Class
import Control.Monad.Trans.CRes
import Control.Monad.Trans.YRes
import Control.Monad.Trans.ResumpUp as RUp

import Data.HFunctor
import Data.Iso

-- TODO: Operations of the form @sig (m (Up a)) -> m (Up a)@ should probably be a new 
-- operation family.

-- | Signature for the restricted par operation
data ParUp (f :: * -> *) x where
  ParUp :: forall y x f. f (Up y) -> f (Up y) -> (Up y -> x) -> ParUp f x
  
instance Functor (ParUp f) where
  fmap f (ParUp p q k) = ParUp p q (f . k) 

instance HFunctor ParUp where
  hmap f (ParUp p q k) = ParUp (f p) (f q) k 

-- | Restricted par operation
parUp :: Member ParUp sig => Prog sig (Up x) -> Prog sig (Up x) -> Prog sig (Up x)
parUp p q = call' (ParUp p q id)

-- | The operation `par` on `CResT` needs to perform pattern matching on the resumption
-- monad, but `CResUpT` can't be pattern matched. Therefore here we simply
-- `down` the two processes and perform `par` at the object level. As a result,
-- the two processes have to return an Up-type.
parResUp :: forall n m a x. (n $~> m, Monad n, Monad m, Action a) 
         => Algebra '[UpOp m, CodeGen] n 
         -> CResUpT (Up a) n (Up x) -> CResUpT (Up a) n (Up x) -> CResUpT (Up a) n (Up x)
parResUp oalg p q = 
  do lhs <- lift (genLetM oalg (down @_ @(CResT a m) p))
     rhs <- lift (genLetM oalg (down @_ @(CResT a m) q))
     upResAlg oalg ([|| $$lhs `par` $$rhs ||])

-- | Algebra transformer for the resumption monad transformer for concurrency.
cResUpAT :: forall m a . (Action a, Monad m)
         => AlgTrans '[UpOp (CResT a m), Empty, Choose, ParUp, Act (Up a)] 
                     '[UpOp m, CodeGen] 
                     '[CResUpT (Up a)] 
                      (MonadDown m)
cResUpAT = AlgTrans $ \oalg -> \case
  (prj -> Just (Alg (UpOp o k)))   -> bwd upIso (upResAlg oalg) (Alg (UpOp o k))
  (prj -> Just (Alg Empty))        -> empty
  (prj -> Just (Scp (Choose x y))) -> x <|> y
  (prj -> Just (ParUp p q k))      -> fmap k (parResUp oalg p q)
  (prj -> Just (Alg (Act (a :: (Up a)) p))) -> RUp.prefix a (return p)

-- | Algebra transformer for the resumption monad transformer for yielding.
yResUpAT :: forall m a b . (Monad m)
         => AlgTrans '[UpOp (YResT a b m), Yield (Up a) (Up b), MapYield (Up a) (Up b)] 
                     '[UpOp m, CodeGen] 
                     '[YResUpT (Up a) (Up b)] 
                      (MonadDown m)
yResUpAT = AlgTrans $ \oalg -> \case
  (prj -> Just (Alg (UpOp o k)))       -> bwd upIso (upResAlg oalg) (Alg (UpOp o k))
  (prj -> Just (Alg (Yield a p)))      -> RUp.yield a (return . p)
  (prj -> Just (Scp (MapYield f g p))) -> RUp.mapYield f g p