{-# LANGUAGE TemplateHaskell, LambdaCase, UndecidableInstances, TypeFamilies #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms, QuantifiedConstraints, LiberalTypeSynonyms #-}
module Control.Effect.CodeGen.Up where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Split
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.Down
import Control.Monad.Trans.Push as P
import Control.Monad.Trans.List
import Control.Monad.Trans.ResUp

import Data.Iso as Iso
import Data.HFunctor
import Data.Functor ((<&>))
import Control.Monad (liftM, ap)

import qualified Control.Effect.Maybe as Mb 
import qualified Control.Effect.Except as Ex
import qualified Control.Effect.State.Lazy as LS
import qualified Control.Effect.State.Strict as SS
import qualified Control.Effect.Reader as R
import Control.Monad.Trans.Resump
import Control.Monad.Trans.Class

type UpOp :: (* -> *) -> Effect
type UpOp m = Alg (UpOp_ m)

data UpOp_ (m :: * -> *) (x :: *) where
  UpOp_   :: Up (m a) -> (Up a -> x) -> UpOp_ m x

  -- | The constructor @UpOpId c@ means the same thing as @UpOp_ c id@ and
  -- @UpOpId@ exists so that `CacheT` can remember up-operations that don't have an
  -- (pure) continuation Up a -> k@ at tail positions of monads, which can then 
  -- be downed trivially. In particular, this allows us to generate tail recursive
  -- code without doing special things in the meta effectful program (tail-recursive
  -- calls can just be @up [|| self ||]@ like other recursive calls).
  -- 
  -- Except for `CacheT`, other monad transformers don't need to care about @UpOpId@,
  -- and the pattern synonym `UpOp` below can be used to deal with @UpOpId@ transparently.
  UpOpId  :: Up (m a) -> UpOp_ m (Up a)

upView :: UpOp_ m x -> UpOp_ m x
upView (UpOpId o) = (UpOp_ o id)
upView x = x

pattern UpOp :: Up (m a) -> (Up a -> x) -> UpOp_ m x
pattern UpOp c k <- (upView -> UpOp_ c k) where 
  UpOp c k = UpOp_ c k

instance Functor (UpOp_ m) where
  fmap f (UpOp o k) = UpOp o (f . k)

-- | An @UpOp m@-operation on a functor @n@ is the same as a function @∀ x. Up (m x) -> n (Up x)@,
-- which is Andras's original formulation of the up operation.
upIso :: forall n m. Functor n => Iso (forall x. UpOp m n x -> n x) (forall x. Up (m x) -> n (Up x))
upIso = Iso fwd bwd where
  fwd :: (forall x. UpOp m n x -> n x) -> (forall x. Up (m x) -> n (Up x))
  fwd o1 umx = o1 (Alg (UpOpId umx))

  bwd :: (forall x. Up (m x) -> n (Up x)) -> (forall x. UpOp m n x -> n x) 
  bwd o2 (Alg (UpOp uma k)) = fmap k (o2 uma)

upAlgIso :: forall n m. Functor n => Iso (Algebra '[UpOp m] n)  (forall x. Up (m x) -> n (Up x))
upAlgIso = trans singAlgIso upIso 

{-# INLINE up #-}
up :: forall sig m a . (Member (UpOp m) sig) => Up (m a) -> Prog sig (Up a) 
up = Iso.fwd upIso call'

{-# INLINE up' #-}
up' :: Member (UpOp m) sig => Up (m a) -> (Up a -> x) -> Prog sig x 
up' u k = call' (Alg (UpOp u k))

upM :: forall m sig n a . (Member (UpOp m) sig, Functor n) 
    => Algebra sig n -> Up (m a) -> n (Up a) 
upM alg = Iso.fwd upIso (callM' alg)

upM' :: Member (UpOp m) sig => Algebra sig n -> Up (m a) -> (Up a -> x) -> n x 
upM' alg u k = callM' alg (Alg (UpOp u k))

upMaybe :: AlgTrans '[UpOp (Mb.MaybeT l)] '[UpOp l, Mb.Throw, CodeGen] '[] Monad
upMaybe = interpretAT1 $ \(Alg (UpOp la k)) ->
  do mb <- up [|| Mb.runMaybeT $$la ||] 
     genCase mb $ \case
       Nothing -> Mb.throw
       Just a  -> return (k a)

upExcept :: forall e l. AlgTrans '[UpOp (Ex.ExceptT e l)] '[UpOp l, Ex.Throw (Up e), CodeGen] '[] Monad
upExcept = interpretAT1 $ \(Alg (UpOp la k)) ->
  do ex <- up [|| Ex.runExceptT $$la ||] 
     genCase ex $ \case
       Left e -> Ex.throw e
       Right a  -> return (k a)

upStateLazy :: forall s l.
  AlgTrans '[UpOp (LS.StateT s l)] '[UpOp l, LS.Put (Up s), LS.Get (Up s), CodeGen] '[] Monad
upStateLazy = interpretAT1 $ \(Alg (UpOp la k)) ->
  do cs <- LS.get @(Up s)
     as <- up [|| LS.runStateT $$la $$cs ||]
     (a, s) <- split as
     LS.put s
     return (k a)

upState :: forall s l.
  AlgTrans '[UpOp (SS.StateT s l)] '[UpOp l, SS.Put (Up s), SS.Get (Up s), CodeGen] '[] Monad
upState = interpretAT1 $ \(Alg (UpOp la k)) ->
  do cs <- SS.get @(Up s)
     as <- up [|| SS.runStateT $$la $$cs ||]
     (a, s) <- split as
     SS.put s
     return (k a)

upReader :: forall r l. AlgTrans '[UpOp (R.ReaderT r l)] '[UpOp l, R.Ask (Up r), CodeGen] '[] Monad
upReader = interpretAT1 $ \(Alg (UpOp la k)) ->
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
  let cons a ms = $$(down (c [||a||] (upMN [|| ms ||])))
      nil       = $$(down n)
  in foldListT cons nil $$cl ||]
  where
    upMN :: forall x. Up (m x) -> n (Up x) 
    upMN = Iso.fwd upAlgIso oalg

-- | A special case of `upPushAlg` for upping lists and avoiding generating
-- the conversions between @[a]@ and @ListT Identity a@.
upListPushAlg :: forall m n a. (Monad m, Functor n, n $~> m) 
              => Algebra '[UpOp m] n 
              -> Up [a] -> PushT n (Up a)
upListPushAlg oalg cl = PushT $ \c n -> upMN 
  [|| foldr (\a ms -> $$(down (c [||a||] (upMN [|| ms ||]) ))) $$(down n) $$cl ||]
  where
    upMN :: forall x. Up (m x) -> n (Up x) 
    upMN = Iso.fwd upAlgIso oalg

-- | A further special case of `upListPushAlg` for `PushT` applied to `Gen`. The
-- version here doesn't generate `Identity` wrappers.
upListPushGenAlg :: forall a. Up [a] -> PushT Gen (Up a)
upListPushGenAlg cl = PushT $ \c n -> return
  [|| foldr (\a ms -> $$(runGen (c [||a||] (return [|| ms ||]) ))) $$(runGen n) $$cl ||]
  
upPush :: forall m. Monad m => AlgTrans '[UpOp (ListT m), UpOp []] '[UpOp m] '[PushT] (MonadDown m)
upPush = AlgTrans $ \oalg -> \case
  (prj -> Just (Alg (UpOp o k))) -> bwd upIso (upPushAlg oalg) (Alg (UpOp o k))
  (prj -> Just (Alg (UpOp o k))) -> bwd upIso (upListPushAlg oalg) (Alg (UpOp o k))

upResAlg :: forall m n s l a. 
            ( Monad n, Monad m, Functor s, Functor l, n $~> m,
              forall x. Split (s x) (l (Up x)) )
         => Algebra '[UpOp m, CodeGen] n 
         -> Up (ResT s m a) -> ResUpT l n (Up a)
upResAlg oalg cr = ResUpT $ \k1 k2 -> upMN 
  [|| foldRes (\a -> $$(down (k1 [||a||]))) 
              (\sm -> $$(down @n @m ((fmap k2 (fmap (fmap upMN) (upSL [||sm||]))) >>= id))) 
              $$cr ||]
  where
    upMN :: forall x. Up (m x) -> n (Up x) 
    upMN = Iso.fwd upAlgIso (oalg . injs)

    upSL :: forall x. Up (s x) -> n (l (Up x))
    upSL = liftGenA oalg . genSplit

upRes :: forall m s l. (Monad m, Functor s, Functor l, forall x. Split (s x) (l (Up x)))
      => AlgTrans '[UpOp (ResT s m)] '[UpOp m, CodeGen] '[ResUpT l] (MonadDown m)
upRes = algTrans1 (\oalg -> bwd upIso (upResAlg oalg))


-- * Resetting code generation

-- | @`down` :: n (Up x) -> Up (m x)@ is not an operation but a co-operation for @n@,
-- so we can't have syntactic down-operations in effectful programs, but we can
-- have the following `reset` operation that is handled to `up . down` by `resetAT`.
-- This effectively merges different branches of code generation and thus is useful 
-- for keeping code size under control.
-- The module "Control.Effect.CodeGen.Merge" serves for the same purpose but generates
-- more compact code (at the cost of being much more complex); see Section 3.5 of Andras'
-- paper (where the operation is called @join@).

data Reset (f :: * -> *) x where
  Reset :: forall y x f. f (Up y) -> (Up y -> x)  -> Reset f x

instance Functor (Reset f) where
  fmap f (Reset o k) = Reset o (f . k) 

instance HFunctor Reset where
  hmap f (Reset o k) = Reset (f o) k 

reset :: forall x sig. Member Reset sig 
      => Prog sig (Up x) -> Prog sig (Up x)
reset p = call' (Reset p id)

resetAT :: forall m. AlgTrans '[Reset] '[UpOp m] '[] (MonadDown m)
resetAT = algTrans1 $ \(oalg :: Algebra '[UpOp m] n) (Reset p k) -> 
  upM' oalg (down @n @m p) k

-- | A variant of `resetAT` that generates a let-binding to make code look nicer. 
resetAT' :: forall m. AlgTrans '[Reset] '[UpOp m, CodeGen] '[] (MonadDown m)
resetAT' = algTrans1 $ \(oalg :: Algebra '[UpOp m, CodeGen] n) (Reset p k) -> 
  do c <- genLetM oalg (down @n @m p) 
     upM' oalg c k

-- * Free Up monad transformer

-- | @FreeUpT m n@ is the monad of interleaving the monad @n@ with object-level @m@-operations.
type FreeUpT m = ResT (UpOp_ m)

instance (Functor n, Monad m, n $~>> m) => FreeUpT m n $~> m where
  down (ResT n) = downTail n' where
    n' = n <&> \case
           Left a           -> Left a
           Right (UpOp c k) -> Right [|| do a <- $$c; $$(down (k [|| a ||])) ||]

upFreeAlg :: Monad n => Up (m x) -> FreeUpT m n (Up x)
upFreeAlg m = ResT (return (Right (UpOp m return))) 

upFree :: forall m. AlgTrans '[UpOp m] '[] '[FreeUpT m] Monad
upFree = algTrans1 $ \_ -> Iso.bwd upIso upFreeAlg

freeUpScp :: forall m n metasig objsig. 
             (Monad n, FreeUpT m n $~> m, Functor metasig, metasig $~> objsig) 
          => (forall x. Up (objsig (m x) -> m x))
          -> (forall x. metasig (FreeUpT m n (Up x)) -> FreeUpT m n (Up x))
freeUpScp objalg o =
  let objop = down @metasig @objsig (fmap (down @(FreeUpT m n) @m) o) 
  in upFreeAlg [|| $$objalg $$objop ||]

-- * Caching the last Up-operations at tail positions

data CacheS m n a where
  Hit :: Up (m a) -> n (Up a) -> CacheS m n (Up a)
  Mis :: a -> CacheS m n a

newtype CacheT m n a = CacheT { unCacheT :: n (CacheS m n a) }

cacheConversion :: forall m n a. Monad n => Iso (CacheT m n a) (n a)
cacheConversion = Iso forget embed where
  forget :: CacheT m n a -> n a
  forget nc = unCacheT nc >>= \case
                Hit _ n -> n
                Mis a   -> return a
  
  embed :: n a -> CacheT m n a 
  embed = CacheT . fmap Mis

instance Monad n => Functor (CacheT m n) where
  fmap = liftM

instance Monad n => Applicative (CacheT m n) where
  pure x = CacheT (return (Mis x))
  (<*>) = ap

instance Monad n => Monad (CacheT m n) where
  return = pure 
  CacheT n >>= k = CacheT $ 
    n >>= \case
      Mis a     -> unCacheT (k a)
      Hit _ n'  -> n' >>= unCacheT . k 

instance MonadTrans (CacheT m) where
  lift = Iso.bwd cacheConversion

instance Functor sig => Forward (Scp sig) (CacheT m) where
  fwd alg op = Iso.bwd cacheConversion (alg (hmap (Iso.fwd cacheConversion) op)) 

upCache :: forall m . AlgTrans '[UpOp m] '[UpOp m] '[CacheT m] Monad
upCache = algTrans1 $ \oalg -> \case
  Alg (UpOpId p)  -> CacheT (return (Hit p (upM oalg p)))
  Alg (UpOp_ p k) -> CacheT (upM oalg p >>= return . Mis . k)

instance (Functor n, Monad m, n $~>> m) => CacheT m n $~> m where
  down (CacheT n) = downTail $
    n <&> \case Mis a    -> Left a
                Hit c _  -> Right c