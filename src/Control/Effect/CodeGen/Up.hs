{-# LANGUAGE TemplateHaskell, LambdaCase, UndecidableInstances, TypeFamilies #-}
module Control.Effect.CodeGen.Up where

import Control.Effect hiding (fwd)
import Control.Effect.Algebraic
import Control.Effect.Scoped
import Control.Effect.Internal.Handler.LowLevel
import Control.Effect.Internal.Forward.ForwardC
import Control.Effect.Internal.Handler.Type
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Split
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.Down
import Control.Monad.Trans.Push as P
import Control.Monad.Trans.List
import Control.Effect.Nondet 
import Data.Iso

import qualified Control.Effect.Maybe as Mb 
import qualified Control.Effect.Except as Ex
import qualified Control.Effect.State.Lazy as LS
import qualified Control.Effect.State.Strict as SS
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

upAlgIso :: forall n m. Functor n => Iso (Algebra '[UpOp m] n)  (forall x. Up (m x) -> n (Up x))
upAlgIso = trans singAlgIso upIso 

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

upMaybe :: Handler '[UpOp (Mb.MaybeT l)] '[UpOp l, Mb.Throw, CodeGen] '[] '[]
upMaybe = interpret1 $ \(Alg (UpOp la k)) ->
  do mb <- up [|| Mb.runMaybeT $$la ||] 
     genCase mb $ \case
       Nothing -> Mb.throw
       Just a  -> return (k a)

upExcept :: forall e l. Handler '[UpOp (Ex.ExceptT e l)] '[UpOp l, Ex.Throw (Up e), CodeGen] '[] '[]
upExcept = interpret1 $ \(Alg (UpOp la k)) ->
  do ex <- up [|| Ex.runExceptT $$la ||] 
     genCase ex $ \case
       Left e -> Ex.throw e
       Right a  -> return (k a)

upStateLazy :: forall s l.
  Handler '[UpOp (LS.StateT s l)] 
          '[UpOp l, LS.Put (Up s), LS.Get (Up s), CodeGen]
          '[]
          '[]
upStateLazy = interpret1 $ \(Alg (UpOp la k)) ->
  do cs <- LS.get @(Up s)
     as <- up [|| LS.runStateT $$la $$cs ||]
     (a, s) <- split as
     LS.put s
     return (k a)

upStateStrict :: forall s l.
  Handler '[UpOp (SS.StateT s l)] 
          '[UpOp l, SS.Put (Up s), SS.Get (Up s), CodeGen]
          '[]
          '[]
upStateStrict = interpret1 $ \(Alg (UpOp la k)) ->
  do cs <- SS.get @(Up s)
     as <- up [|| SS.runStateT $$la $$cs ||]
     (a, s) <- split as
     SS.put s
     return (k a)

upReader :: Handler '[UpOp (R.ReaderT r l)] 
                    '[UpOp l, R.Ask (Up r), CodeGen] '[] '[]
upReader = interpret1 $ \(Alg (UpOp la k)) ->
  do cr <- R.ask
     a <- up [|| R.runReaderT $$la $$cr ||]
     return (k a)

{-
-- The following is wrong because it generates infinitely branches of pattern matching.
-- The right thing to do is to use PushT as the compile-time version of ListT.

upNdet :: Handler '[UpOp (ND.ListT l)] '[UpOp l, ND.Choose, ND.Empty, CodeGen] '[] '[]
upNdet = interpret1 $ 
  let go (Alg (UpOp la k)) =
         do a <- up [|| ND.runListT $$la ||]
            genCase a $ \case
              Nothing -> ND.stop
              (Just am) -> do (ca, cm) <- split am
                              return (k ca) ND.<|> go (Alg (UpOp cm k))
  in go
-}

upPushAlg :: forall m n a. (Monad m, Functor n, n $~> m) 
          => Algebra '[UpOp m] n 
          -> Up (ListT m a) -> PushT n (Up a)
upPushAlg oalg cl = PushT $ \c n -> upMN [|| 
  foldListT (\a ms -> $$(down (c [||a||] (upMN [|| ms ||])))) 
            $$(down n) $$cl ||]
  where
    upMN :: forall x. Up (m x) -> n (Up x) 
    upMN = fwd upAlgIso oalg

-- | A variant that generates two let-bindings for readability
upPushAlg' :: forall m n a. (Monad m, Functor n, n $~> m) 
          => Algebra '[UpOp m] n 
          -> Up (ListT m a) -> PushT n (Up a)
upPushAlg' oalg cl = PushT $ \c n -> upMN [|| 
  let cons a ms = $$(down (c [||a||] (upMN [|| ms ||])))
      nil       = $$(down n)
  in foldListT cons nil $$cl ||]
  where
    upMN :: forall x. Up (m x) -> n (Up x) 
    upMN = fwd upAlgIso oalg

class (Monad n, n $~> m) => PushC m n where
instance (Monad n, n $~> m) => PushC m n where

instance ForwardC Monad effs t => ForwardC (PushC m) effs t where
  fwdC = fwdC @Monad @effs @t

pushAlg :: forall m n. (Monad m, Functor n, n $~> m) 
        => Algebra '[UpOp m] n
        -> Algebra '[UpOp (ListT m), Empty, Choose, Once] (PushT n)
pushAlg oalg op
  | (Just (Alg (UpOp o k))) <- prj op = bwd upIso (upPushAlg oalg) (Alg (UpOp o k))
  | (Just (Alg Empty))      <- prj op = empty
  | (Just (Scp (Choose x y))) <- prj op = x <|> y
  | (Just (Scp (Once x))) <- prj op   = P.once x

pushAT :: Monad m => AlgTrans '[UpOp (ListT m), Empty, Choose, Once] '[UpOp m] '[PushT] (PushC m)
pushAT = AlgTrans $ pushAlg


{-
The following is up and down for the special case @PushT Gen@.
If you are puzzled by the general case, having a look at the special version may
be helpful. I will keep it here for a while for playing.
-}

newtype LG a  = LG {runLG :: forall t. (a -> Gen (Up t) -> Gen (Up t)) 
                          -> Gen (Up t) -> Gen (Up t)}

instance Functor LG where
  fmap f lg = do x <- lg; return (f x)

instance Applicative LG where
  f <*> x = do f' <- f; x' <- x; return (f' x') 
  pure x = LG $ \c n -> c x n
instance Monad LG where
  lg >>= k = LG $ \c n -> runLG lg (\a as -> runLG (k a) c as) n

upLG :: Up [a] -> LG (Up a)
upLG cl = LG $ \c n -> upGen [|| 
  foldr (\a ms -> $$(downGen (c [||a||] (upGen [||ms||])))) 
        $$(downGen n)   
        $$cl  
  ||]

downLG :: LG (Up a) -> Up [a]
downLG lg = downGen (runLG lg (\a gas -> fmap (\as -> [|| $$a : $$as ||]) gas) (upGen [||[]||])) 

upGen :: forall a. Up a -> Gen (Up a)
upGen c = return c

downGen :: forall a. Gen (Up a) -> Up a
downGen g = unGen g id