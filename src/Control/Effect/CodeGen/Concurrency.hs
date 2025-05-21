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
import Control.Monad.Trans.ResUp as RUp

import Data.HFunctor
import Data.Iso

-- TODO: Operations of the form @sig (m (Up a)) -> m (Up a)@ should probably be a new 
-- operation family.
data ParUp (f :: * -> *) x where
  ParUp :: forall y x f. f (Up y) -> f (Up y) -> (Up y -> x) -> ParUp f x
  
instance Functor (ParUp f) where
  fmap f (ParUp p q k) = ParUp p q (f . k) 

instance HFunctor ParUp where
  hmap f (ParUp p q k) = ParUp (f p) (f q) k 

-- | The operation `par` on `CResT` needs to perform pattern matching on the resumption
-- monad, but `CResUpT` can't be pattern matched, so I don't know how to support 
-- @par@ on `CResUpT`. Therefore here we simply `down` the two processes and perform
-- `par` at the object level. As a result, the two processes have to return an Up-type.

parResUp :: forall n m a x. (n $~> m, Monad n, Monad m, Action a) 
         => Algebra '[UpOp m, CodeGen] n 
         -> CResUpT (Up a) n (Up x) -> CResUpT (Up a) n (Up x) -> CResUpT (Up a) n (Up x)
parResUp oalg p q = 
  do lhs <- lift (genLetM oalg (down @_ @(CResT a m) p))
     rhs <- lift (genLetM oalg (down @_ @(CResT a m) q))
     upResAlg oalg ([|| $$lhs `par` $$rhs ||])

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

yResUpAT :: forall m a b . (Monad m)
         => AlgTrans '[UpOp (YResT a b m), Yield (Up a) (Up b), MapYield (Up a) (Up b)] 
                     '[UpOp m, CodeGen] 
                     '[YResUpT (Up a) (Up b)] 
                      (MonadDown m)
yResUpAT = AlgTrans $ \oalg -> \case
  (prj -> Just (Alg (UpOp o k)))       -> bwd upIso (upResAlg oalg) (Alg (UpOp o k))
  (prj -> Just (Alg (Yield a p)))      -> yieldUp a (return . p)
  (prj -> Just (Scp (MapYield f g p))) -> mapYieldUp f g p