{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Cut where

import Control.Effect
import Control.Effect.Nondet
import Control.Handler
import Control.Family.AlgScp
import Prelude hiding (or)

import Data.CutList ( CutListT(..), CutListT'(..), fromCutListT' )
import Data.HFunctor ( HFunctor(..) )
import Control.Applicative ( Alternative((<|>), empty) )

{-
Idea:

Nondeterminism consists of just or and stop.
A model of this is lists, using the list monad transformer.

If we want a notion of backtracking, we must include
a new operation, like `try`, which can be interpreted
as executing `once`, many times etc.

One way to interpret `once` is into the list monad directly.
An alternative is to interpet `once` into `cutFail` and `cutCall`,
which can then be interpreted using a `CutList`.
-}

data CutFail' a where
  CutFail :: CutFail' a
  deriving Functor

type CutFail = Algebraic CutFail'

cutFail :: Member CutFail sig => Prog sig a
cutFail = injCall (Algebraic CutFail)

data CutCall' a where
  CutCall :: a -> CutCall' a
  deriving Functor

type CutCall = Scoped CutCall'

cut :: (Members [Or, CutFail] sig) => Prog sig ()
cut = or skip cutFail

cutCall :: Member CutCall sig => Prog sig a -> Prog sig a
cutCall p = cutCall' progAlg p -- injCall (Scp (CutCall (fmap return p)))

cutCall' :: (Monad m, Member CutCall sig)
  => (forall a . Effs sig m a -> m a) -> m a -> m a
cutCall' alg p = (alg . inj) (Scoped (CutCall p))

skip :: Monad m => m ()
skip = return ()

callAlg :: Monad m => CutListT m a -> CutListT m a
callAlg (CutListT mxs) = CutListT $
  do xs <- mxs
     case xs of
       x :<< mys -> return (x :<< runCutListT (callAlg (CutListT mys)))
       NilT      -> return NilT
       ZeroT     -> return NilT   -- clear the cut flag at the boundary of call

cutListFwd
  :: (Monad m, Functor lsig)
  => (forall x . lsig (m x) -> m x)
  -> (forall x . lsig (CutListT m x) -> CutListT m x)
cutListFwd alg x = CutListT (alg (fmap runCutListT x))

cutListAlg
  :: Monad m => (forall x. oeff m x -> m x)
  -> forall x. Effs [Stop, Or, CutFail, CutCall] (CutListT m) x -> CutListT m x
cutListAlg oalg op
  | Just (Algebraic Stop)        <- prj op = empty
  | Just (Algebraic (Or x y))    <- prj op = return x <|> return y
  | Just (Algebraic CutFail)     <- prj op = CutListT (return ZeroT)
  | Just (Scoped (CutCall x))    <- prj op = callAlg x

cutList :: ASHandler [Stop, Or, CutFail, CutCall] '[] '[[]]
cutList = ashandler (\_ -> fromCutListT') cutListAlg cutListFwd

instance HFunctor CutListT where
  hmap h (CutListT x) = CutListT (fmap (hmap h) (h x))

instance HFunctor CutListT' where
  hmap _ ZeroT      = ZeroT
  hmap _ NilT       = NilT
  hmap h (x :<< xs) = x :<< fmap (hmap h) (h xs)

onceCut :: Handler '[Once] [CutCall, CutFail, Or] '[] fam
onceCut = interpret' onceCutAlg

onceCutAlg :: forall oeff m . (Monad m , Members [CutCall, CutFail, Or] oeff)
  => (forall x. Effs oeff m x -> m x)
  -> (forall x. Effs '[Once] m x -> m x)
onceCutAlg oalg op
  | Just (Scoped (Once p)) <- prj op
  = cutCall' oalg (do x <- p
                      eval oalg (do cut
                                    return x))

onceNondet :: ASHandler [Once, Stop, Or, CutFail, CutCall] '[] '[[]]
onceNondet = fuse onceCut cutList
