{-# LANGUAGE TemplateHaskell, LambdaCase #-}
module Control.Effect.CodeGen.Up where

import Control.Effect hiding (fwd)
import Control.Effect.Algebraic
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Split
import Control.Effect.CodeGen.Gen
import Data.Iso

import qualified Control.Effect.Maybe as Mb 
import qualified Control.Effect.Except as Ex
import qualified Control.Effect.State.Lazy as LS
import qualified Control.Effect.State.Strict as SS
import qualified Control.Effect.Nondet as ND
import qualified Control.Effect.Alternative as ND
import qualified Control.Effect.Reader as R

type UpOp :: (* -> *) -> Effect
type UpOp m = Alg (UpOp_ m)

data UpOp_ (m :: * -> *) (x :: *) where
  UpOp :: Up (m a) -> (Up a -> x) -> UpOp_ m x

instance Functor (UpOp_ m) where
  fmap f (UpOp o k) = UpOp o (f . k)

-- | An @UpOp m@-operation on a functor @n@ is the same as a function @∀ x. Up (m x) -> n (Up x)@,
-- which is Andras's original formulation of the up operation.
upIso :: forall n m. Functor n => Iso (forall x. UpOp m n x -> n x) (forall x. Up (m x) -> n (Up x))
upIso = Iso fwd bwd where
  fwd :: (forall x. UpOp m n x -> n x) -> (forall x. Up (m x) -> n (Up x))
  fwd o1 umx = o1 (Alg (UpOp umx id))

  bwd :: (forall x. Up (m x) -> n (Up x)) -> (forall x. UpOp m n x -> n x) 
  bwd o2 (Alg (UpOp uma k)) = fmap k (o2 uma)

upAlgIso :: Functor n => Iso (Algebra '[UpOp m] n)  (forall x. Up (m x) -> n (Up x))
upAlgIso = trans singAlgIso upIso 

upGenAlg :: Algebra '[UpOp Identity] Gen
upGenAlg = bwd upAlgIso (\cm -> return [||runIdentity $$cm||])

{-# INLINE up #-}
up :: forall sig m a . (Member (UpOp m) sig) => Up (m a) -> Prog sig (Up a) 
up = fwd upIso call'

{-# INLINE up' #-}
up' :: (Member (UpOp m) sig) => Up (m a) -> (Up a -> x) -> Prog sig x 
up' u k = call' (Alg (UpOp u k))

-- The following handler can also be rephrased slightly more specially as 
--
--   upMaybe :: Monad n => Algebra '[UpOp m] n -> Algebra '[UpOp (MaybeT m)] (MaybeT n)
--
-- I am not sure which one is better.

upMaybe :: Handler '[UpOp (Mb.MaybeT l)] '[UpOp l, Mb.Throw, LiftGen] IdentityT Identity
upMaybe = interpret1 $ \(Alg (UpOp la k)) ->
  do mb <- up [|| Mb.runMaybeT $$la ||] 
     caseM mb $ \case
       Nothing -> Mb.throw
       Just a  -> return (k a)

upExcept :: forall e l. Handler '[UpOp (Ex.ExceptT e l)] '[UpOp l, Ex.Throw (Up e), LiftGen] IdentityT Identity
upExcept = interpret1 $ \(Alg (UpOp la k)) ->
  do ex <- up [|| Ex.runExceptT $$la ||] 
     caseM ex $ \case
       Left e -> Ex.throw e
       Right a  -> return (k a)

upStateLazy :: forall s l.
  Handler '[UpOp (LS.StateT s l)] 
          '[UpOp l, LS.Put (Up s), LS.Get (Up s), LiftGen]
          IdentityT 
          Identity
upStateLazy = interpret1 $ \(Alg (UpOp la k)) ->
  do cs <- LS.get @(Up s)
     as <- up [|| LS.runStateT $$la $$cs ||]
     (a, s) <- split as
     LS.put s
     return (k a)

upStateStrict :: forall s l.
  Handler '[UpOp (SS.StateT s l)] 
          '[UpOp l, SS.Put (Up s), SS.Get (Up s), LiftGen]
          IdentityT 
          Identity
upStateStrict = interpret1 $ \(Alg (UpOp la k)) ->
  do cs <- SS.get @(Up s)
     as <- up [|| SS.runStateT $$la $$cs ||]
     (a, s) <- split as
     SS.put s
     return (k a)

upReader :: Handler '[UpOp (R.ReaderT r l)] 
                    '[UpOp l, R.Ask (Up r), LiftGen] IdentityT Identity
upReader = interpret1 $ \(Alg (UpOp la k)) ->
  do cr <- R.ask
     a <- up [|| R.runReaderT $$la $$cr ||]
     return (k a)

{-
-- The following is wrong because it generates infinitely branches of pattern matching.
-- The right thing to do is to generalise from Gen to GenT 
--   
--   newtype GenT m a = GenT { runGenT :: forall r. (a -> Up (m r)) -> Up (m r) } 
--
-- so that we could have a trivial
-- 
--   up :: Up (ListT l a) -> GenT (ListT l) (Up a)
--   up c = GenT (\@r (k :: Up a -> Up (ListT l r)) -> [|| do a <- $$c; $$(k [||a||])  ||] )
--
-- that embeds an object monadic program into the meta world without pattern matching. 

upNdet :: Handler '[UpOp (ND.ListT l)] '[UpOp l, ND.Choose, ND.Empty, LiftGen] IdentityT Identity
upNdet = interpret1 $ 
  let go (Alg (UpOp la k)) =
         do a <- up [|| ND.runListT $$la ||]
            caseM a $ \case
              Nothing -> ND.stop
              (Just am) -> do (ca, cm) <- split am
                              return (k ca) ND.<|> go (Alg (UpOp cm k))
  in go
-}