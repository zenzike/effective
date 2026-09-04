{-|
Module      : Control.Effect.CodeGen.Concurrency
Description : Algebra transformers for staging concurrency
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains algebra transformers for t`ResUpT`, the monad transformer to be
used at the meta level for resumption. The monad transformer t`ResUpT` can be downed
to and upped from the (object-level) resumption monad transformer @ResT@.
Moreover, for every functor @s@, the monad @ResUpT s n@ supports algebraic
operations of signature @s@ in the same way as @ResT s@.

However, we also have operations on @ResT s m@ that are defined by pattern matching
and recursion, such as @parL@ in "Control.Monad.Trans.CRes". These operations can't
be implemented on @ResUpT@ because @ResUpT@ doesn't support pattern matching.

An imperfect workaround is to have a /restricted version/ of these operations at the meta
level, such as @parUp :: m (CodeQ x) -> m (CodeQ x) -> m (CodeQ x)@ where the return value
must be code, and t`ResUpT` supports operations like this by downing
the arguments to the object level, invoking the object-level algebra, and then upping
the result back to the meta level. This is of course very unsatisfactory but currently
I don't know how to do better.
-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}

module Control.Effect.CodeGen.Concurrency where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped

import Control.Effect.CodeGen.Operations
import Control.Effect.CodeGen.ScopedC
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Down
import Control.Effect.Yield
import Control.Effect.Concurrency.Operations hiding (par)
import Control.Effect.Nondet

import Control.Monad.Trans.Class
import Control.Monad.Trans.CRes
import Control.Monad.Trans.YRes
import Control.Monad.Trans.ResumpUp as RUp
import Control.Concurrent (forkIO)

import Data.Kind (Type)
import Data.Iso

-- | Underlying first-order signature for staged parallel composition.
data ParUp_ k = ParUp_ k k deriving Functor

type ParUp = ScpC ParUp_

pattern ParUp x y k = ScpC (ParUp_ x y) k

pattern ParUp' :: f x -> f x -> Scp ParUp_ f x
pattern ParUp' x y = Scp (ParUp_ x y)

instance ParUp_ $~> ParUp_ where
  down (ParUp_ x y) = [|| ParUp_ $$x $$y ||]

-- | Staged par operation
parUp :: Member ParUp eff => Prog eff (CodeQ x) -> Prog eff (CodeQ x) -> Prog eff (CodeQ x)
parUp p q = call (ParUp p q id)

-- | Par operation on @GenM IO@ using the native implementation of `forkIO`
parGenIO :: Par (GenM IO) x -> GenM IO x
parGenIO (Par p q) = GenM $ \k ->
  [|| do let childProc = $$(runGenM (fmap (const [|| () ||]) q))
         forkIO childProc
         $$(unGenM p k)
  ||]

-- | The operation `par` on `CResT` needs to perform pattern matching on the resumption
-- monad, but `CResUpT` can't be pattern matched. Therefore here we simply
-- `down` the two processes and perform `par` at the object level. As a result,
-- the two processes have to return a CodeQ type.
parResUp
  :: forall n m a x.
     ( n $~> m, Monad n, Monad m, Action a )
  => Algebra '[UpOp m, CodeGen] n
  -> CResUpT (CodeQ a) n (CodeQ x)
  -> CResUpT (CodeQ a) n (CodeQ x)
  -> CResUpT (CodeQ a) n (CodeQ x)
parResUp oalg p q =
  do lhs <- lift (genLetM oalg (down @_ @(CResT a m) p))
     rhs <- lift (genLetM oalg (down @_ @(CResT a m) q))
     upResAlg oalg ([|| $$lhs `par` $$rhs ||])

-- | Algebra transformer for the resumption monad transformer for concurrency.
cResUpAT
  :: forall m a.
     ( Action a, Monad m )
  => AlgTrans '[UpOp (CResT a m), Empty, Choose, ParUp, Act (CodeQ a)]
              '[UpOp m, CodeGen]
              '[CResUpT (CodeQ a)]
              (MonadDown m)
cResUpAT = AlgTrans $ \oalg ->
  (\(Alg (UpOp o k))         -> bwd upIso (upResAlg oalg) (Alg (UpOp o k))) :#
  (\(Alg Empty_)             -> empty) :#
  (\(Scp (Choose_ x y))      -> x <|> y) :#
  (\(ParUp p q k)            -> fmap k (parResUp oalg p q)) :#.
  (\(Act (a :: (CodeQ a)) p) -> RUp.prefix a (return p))

-- | Algebra transformer for the resumption monad transformer for yielding.
yResUpAT
  :: forall m a b.
     (Monad m)
  => AlgTrans '[UpOp (YResT a b m), Yield (CodeQ a) (CodeQ b), MapYield (CodeQ a) (CodeQ b)]
              '[UpOp m, CodeGen]
              '[YResUpT (CodeQ a) (CodeQ b)]
              (MonadDown m)
yResUpAT = AlgTrans $ \oalg ->
  (\(Alg (UpOp o k))        -> bwd upIso (upResAlg oalg) (Alg (UpOp o k))) :#
  (\(Alg (Yield_ a p))      -> RUp.yield a (return . p)) :#.
  (\(Scp (MapYield_ f g p)) -> RUp.mapYield f g p)
