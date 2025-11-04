{-|
Module      : Control.Effect.CodeGen.Up
Description : Reflecting object-level programs to the meta level.
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

For an object-level monad @m@ and a meta-level monad @n@, a function
@forall x. Up (m x) -> n (Up x)@ is called an @m@-up operation on @n@.
Such an operation serves the purpose of \'reflecting\' object-level program
back into meta level. This is needed when we want to generate object-level
programs that calls other object-level programs.
For example, suppose we want to generate the following function @q@:

> p :: StateT Int Identity Int
> p = do put 0; q; get

where @q :: StateT Int Identity Int@ is some other program (possibly also
generated from a meta-program). When writing the /meta-program/ that generates
@p@, we need a way to call the object-level @q@, and this is where an
up-operation is needed.
-}
{-# LANGUAGE TemplateHaskell, LambdaCase, UndecidableInstances, TypeFamilies #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms, QuantifiedConstraints #-}
{-# LANGUAGE ImpredicativeTypes #-}
module Control.Effect.CodeGen.Up where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Family.Distributive
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Split
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.Down
import Control.Monad.Trans.Push as P
import Control.Monad.Trans.List
import Control.Monad.Trans.ResumpUp

import Data.Kind (Type)
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

-- * Reflecting object-level programs to the meta level

-- | An up-operation @Up (m a) -> n (Up a)@ on a monad @n@ is the same as
-- a function @forall x. exists. (Up (m a), Up a -> x) -> n x@, witnessed by `upIso`
-- below. The type of the domain of this function doesn't mention @n@ at all, so this
-- is an algebraic operation on @n@.
type UpOp :: (Type -> Type) -> Effect
type UpOp m = Alg (UpOp_ m)

-- | The (first-order) signature functor for the (algebraic) operation @up@.
data UpOp_ (m :: Type -> Type) (x :: Type) where
  -- | Using left-Kan extension, functions @forall x. Up (m x) -> n (Up x)@
  -- are in bijection with @forall x. exists. (Up (m a), Up a -> x) -> n x@.
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

-- | Turn `UpOpId` into an ordinary `UpOp_`.
upView :: UpOp_ m x -> UpOp_ m x
upView (UpOpId o) = (UpOp_ o id)
upView x = x

-- | Using the pattern @UpOp@ we can treat the datatype t`UpOp_` as having
-- one constructor @UpOp :: Up (m a) -> (Up a -> x) -> UpOp_ m x@.
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

-- | Syntactic up-operations on (meta-)programs.
up :: Member (UpOp m) sig => Up (m a) -> Prog sig (Up a)
up = Iso.fwd upIso call

-- | Syntactic up-operations on (meta-)programs with an additional continuation
-- argument @Up a -> x@.
up' :: Member (UpOp m) sig => Up (m a) -> (Up a -> x) -> Prog sig x
up' u k = call (Alg (UpOp u k))

-- | Up-operations on a monad @n@.
upM :: forall m sig n a. (Member (UpOp m) sig, Functor n)
    => Algebra sig n -> Up (m a) -> n (Up a)
upM alg = Iso.fwd upIso (callM alg)

-- | Up-operations on a monad @n@ with an additional continuation argument.
upM' :: Member (UpOp m) sig => Algebra sig n -> Up (m a) -> (Up a -> x) -> n x
upM' alg u k = callM alg (Alg (UpOp u k))

-- * Algebra transformers for the up-operation
--
-- The following are algebra transformers for the up-operation on various monad transformers.
-- The transformers for `MaybeT`, `EitherT`, `ReaderT`, `WriterT`, `StateT` are quite
-- simple: object-level monadic programs are turned into meta-level by generating case
-- splits (aka \'the trick\'  in meta-programming).
-- The up-operations for `ListT` and `ResT` are much trickier, because we can't generate
-- infinitely many case splits.

-- | To up @MaybeT l@, we need to be able to up @l@, throwing exceptions, and generate case splits.
upMaybe :: AlgTrans '[UpOp (Mb.MaybeT l)] '[UpOp l, Mb.Throw, CodeGen] '[] Monad
upMaybe = interpretAT1 $ \(Alg (UpOp la k)) ->
  do mb <- up [|| Mb.runMaybeT $$la ||]
     genCase mb $ \case
       Nothing -> Mb.throw
       Just a  -> return (k a)

-- | To up @ExceptT l@, we need to be able to up @l@, throwing exceptions, and generate case splits.
upExcept :: forall e l. AlgTrans '[UpOp (Ex.ExceptT e l)] '[UpOp l, Ex.Throw (Up e), CodeGen] '[] Monad
upExcept = interpretAT1 $ \(Alg (UpOp la k)) ->
  do ex <- up [|| Ex.runExceptT $$la ||]
     genCase ex $ \case
       Left e -> Ex.throw e
       Right a  -> return (k a)

-- | To up @State s l@, we need to be able to up @l@, mutate @Up s@, and generate case splits.
upStateLazy :: forall s l.
  AlgTrans '[UpOp (LS.StateT s l)] '[UpOp l, LS.Put (Up s), LS.Get (Up s), CodeGen] '[] Monad
upStateLazy = interpretAT1 $ \(Alg (UpOp la k)) ->
  do cs <- LS.get @(Up s)
     as <- up [|| LS.runStateT $$la $$cs ||]
     (a, s) <- split as
     LS.put s
     return (k a)

-- | To up @State s l@, we need to be able to up @l@, mutate @Up s@, and generate case splits.
upState :: forall s l.
  AlgTrans '[UpOp (SS.StateT s l)] '[UpOp l, SS.Put (Up s), SS.Get (Up s), CodeGen] '[] Monad
upState = interpretAT1 $ \(Alg (UpOp la k)) ->
  do cs <- SS.get @(Up s)
     as <- up [|| SS.runStateT $$la $$cs ||]
     (a, s) <- split as
     SS.put s
     return (k a)

-- | To up @Reader r l@, we need to be able to up @l@, ask @Up r@, and generate case splits.
upReader :: forall r l. AlgTrans '[UpOp (R.ReaderT r l)] '[UpOp l, R.Ask (Up r), CodeGen] '[] Monad
upReader = interpretAT1 $ \(Alg (UpOp la k)) ->
  do cr <- R.ask
     a <- up [|| R.runReaderT $$la $$cr ||]
     return (k a)

-- ** Up-operations for recursively defined monad transformers
--
-- Following the pattern for the monad transformers above, it might be tempting to write the
-- following up-operation for @ListT@, but this is wrong because it generates infinitely branches
-- of pattern matching.
--
-- > upNdet :: AlgTrans '[UpOp (ND.ListT l)] '[UpOp l, ND.Choose, ND.Empty, CodeGen] '[] Monad
-- > upNdet = interpretAT1 $
-- >   let go (Alg (UpOp la k)) =
-- >          do a <- up [|| ND.runListT $$la ||]
-- >             genCase a $ \case
-- >               Nothing -> ND.stop
-- >               (Just am) -> do (ca, cm) <- split am
-- >                               return (k ca) ND.<|> go (Alg (UpOp cm k))
-- >   in go
--
-- Since at the meta level we can't never know how many choices there are in an object-level
-- @ListT@. It seems that we are never able to up an object-level @ListT@ to an meta-level
-- @ListT@.
--
-- However, we can solve this problem by observing that we don't actually need to know at
-- the meta level how many nondeterministic choices there are. All we care about is that
-- we can eventually generate some @ListT@ code. Therefore we replace @ListT@ with the following
-- t`PushT` () at the meta-level:
--
-- > newtype PushT n a = PushT
-- >   { runPushT :: forall t. (a -> n (Up t) -> n (Up t)) -> n (Up t) -> n (Up t) }
-- >
--
-- which is the Church-encoding of `ListT` with the final answer type restricted to be code.
-- This `PushT` supports non-deterministic operations just like regular Church-encoded `ListT`
-- but it also supports @up@ and @down@ with @ListT@.

-- | Given a piece of code of type @ListT m a@, we reflect it back to a meta-level @PushT@
-- by generating a fold of the given @ListT@ and using the two continuation arguments of
-- the @PushT@ in the corresponding two arguments for the fold.

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

-- | Algebra transformer for upping @ListT m a@ and @[a]@. Note that this algebra transformer
-- has `PushT` in its transformer stack, which is different from other algebra transformers
-- of up such as `upState` and `upMaybe`, whose transformer arguments are empty.
-- Therefore the way to use `upPush` is slightly different from the way to use `upStateT`:
-- we write @upState `fuseAT` stateT@ but @upPush `appendAT` pushAT@
-- (or directly `Control.Effect.CodeGen.Nondet.pushWithUpAT`).
upPush :: forall m. Monad m => AlgTrans '[UpOp (ListT m), UpOp []] '[UpOp m] '[PushT] (MonadDown m)
upPush = AlgTrans $ \oalg -> \case
  (prj -> Just (Alg (UpOp o k))) -> bwd upIso (upPushAlg oalg) (Alg (UpOp o k))
  (prj -> Just (Alg (UpOp o k))) -> bwd upIso (upListPushAlg oalg) (Alg (UpOp o k))

-- | The up-operation for the resumption monad transformer. The situation is similar to
-- that of `ListT` and `PushT`. The meta-level correspondent of the resumption monad `ResT`
-- has to be `ResUpT` a restricted Church-encoded version of the resumption monad.
-- Moreover, we also need a meta-level version @l@ of the object-level step functor @s@.
upResAlg :: forall m n s l a.
            ( Monad n, Monad m, n $~> m,
              Functor s, Functor l, forall x. Split (s x) (l (Up x)) )
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

-- | Algebra transformer for upping @ResT s m a@.
upRes :: forall m s l. (Monad m, Functor s, Functor l, forall x. Split (s x) (l (Up x)))
      => AlgTrans '[UpOp (ResT s m)] '[UpOp m, CodeGen] '[ResUpT l] (MonadDown m)
upRes = algTrans1 (\oalg -> bwd upIso (upResAlg oalg))

-- * Resetting code generation

-- | @`down` :: n (Up x) -> Up (m x)@ is not an operation but a co-operation for @n@,
-- so we can't have syntactic down-operations in effectful meta-programs, but we can
-- have the following `reset` operation that is handled to `up . down` by `resetAT`.
-- This effectively merges different branches of code generation and thus is useful
-- for keeping code size under control.
-- The module "Control.Effect.CodeGen.Join" serves for the same purpose but generates
-- more compact code (at the cost of being much more complex).

-- | Signature functor for the reset operation
data Reset (f :: Type -> Type) x where
  Reset :: forall y x f. f (Up y) -> (Up y -> x)  -> Reset f x

instance Functor (Reset f) where
  fmap f (Reset o k) = Reset o (f . k)

instance HFunctor Reset where
  hmap f (Reset o k) = Reset (f o) k

-- | Reset code generation.
reset :: forall x sig. Member Reset sig
      => Prog sig (Up x) -> Prog sig (Up x)
reset p = call (Reset p id)

-- | Resetting is interpreted as @up@ followed by @down@.
resetAT :: forall m. AlgTrans '[Reset] '[UpOp m] '[] (MonadDown m)
resetAT = algTrans1 $ \(oalg :: Algebra '[UpOp m] n) (Reset p k) ->
  upM' oalg (down @n @m p) k

-- | A variant of `resetAT` that generates a let-binding to make code look nicer.
resetAT' :: forall m. AlgTrans '[Reset] '[UpOp m, CodeGen] '[] (MonadDown m)
resetAT' = algTrans1 $ \(oalg :: Algebra '[UpOp m, CodeGen] n) (Reset p k) ->
  do c <- genLetM oalg (down @n @m p)
     upM' oalg c k

-- * FreeUp monad transformer
--
-- We have seen above that upping `ListT` and `ResT` is quite non-trivial and there is
-- in fact a simpler solution. Note that t`UpOp` is an /algebraic/ operation, so we
-- freely adjoin it with any monads using the resumption monad transformer.
-- This gives us the `FreeUpT m` monad transformer below. For every monad @n@, the
-- monad @FreeUpT m n@ supports the operation @UpOp m@, and as usual every algebra
-- operation on @n@ can be forwarded to @FreeUpT m n@.
--
-- However, the downside of this approach is that the scoped operations on @n@
-- can never be meaningfully forwarded to @FreeUpT m n@, because elements of
-- @FreeUpT m n@ are interleaved @n@-computations and @m@-code, and scoped
-- operations on @n@ at the meta-level of course don't know how to deal with
-- object-level @m@-code.
-- An imperfect fix is that if we have the code of an object-level scoped operation
-- @sig (m x) -> m x@, we can define a meta-level operation of type
--
-- > sig (FreeUp m (Up x)) -> FreeUp m (Up x)
--
-- by first downing the arguments to the object level and invoke the object-level
-- scoped operation, and then up result back. This is not ideal because we have missed
-- the opportunity of optimising scoped operation by staging, and also at the meta-level
-- we don't have really scoped operations @sig (FreeUp m n x) -> FreeUp m n x@ but
-- only operations @sig (FreeUp m (Up x)) -> FreeUp m (Up x)@.

-- | @FreeUpT m n@ is the monad of interleaving the monad @n@ with object-level @m@-programs.
newtype FreeUpT m n a = FreeUpT { unFreeUpT :: ResT (UpOp_ m) n a }
  deriving (Functor, Monad, Applicative, MonadTrans)

instance (Functor n, Monad m, n $~>> m) => FreeUpT m n $~>> m where
  downTail (FreeUpT (ResT n)) = downTail $ n <&> \case
    Left (Left a)    -> Left a
    Left (Right b)   -> Right b
    Right (UpOp c k) -> Right [|| do a <- $$c; $$(downTail (FreeUpT (k [|| a ||]))) ||]

instance (Functor n, Monad m, n $~>> m) => FreeUpT m n $~> m where
  down = downTail . fmap Left

-- | Algebra of the up-operation on @FreeUpT m@.
upFreeAlg :: Monad n => Up (m x) -> FreeUpT m n (Up x)
upFreeAlg m = FreeUpT $ ResT (return (Right (UpOp m return)))

-- | Algebra transformer for the up-operation on @FreeUpT@.
upFree :: forall m. AlgTrans '[UpOp m] '[] '[FreeUpT m] Monad
upFree = algTrans1 $ \_ -> Iso.bwd upIso upFreeAlg

-- | Operations on @FreeUpT m n@ obtained from object-level operations on @m@.
freeUpOpAlg :: forall m n meff oeff.
               (Monad n, meff (FreeUpT m n) $~> oeff m)
            => (forall x. Up (oeff m x -> m x))
            -> (forall x. meff (FreeUpT m n) (Up x) -> FreeUpT m n (Up x))
freeUpOpAlg objalg op =
  let objop = down @(meff (FreeUpT m n)) @(oeff m) op
  in upFreeAlg [|| $$objalg $$objop ||]

-- | `freeUpOpAlg` specialised for scoped operations.
freeUpScpAlg :: forall m n metasig objsig.
                (Monad n, FreeUpT m n $~> m, Functor metasig, metasig $~> objsig)
             => (forall x. Up (Scp objsig m x -> m x))
             -> (forall x. Scp metasig (FreeUpT m n) (Up x) -> FreeUpT m n (Up x))
freeUpScpAlg objalg op = freeUpOpAlg objalg op

-- * Caching the last Up-operations at tail positions
--
-- As discussed in the documentation for `($~>>)`, we want to avoid generating unnecessary
-- eta-expansion caused by @down . up@ at tail positions. The class `($~>>)` provided the
-- function @`downTail` :: n (Either (Up x) (Up (m x))) -> Up (m x)@ to achieve this
-- but with just this we need to manually modify our meta-program to change tail @up m@
-- to @return (Right m)@ and all other ordinary returns to @return . Left@.
--
-- This is of course not ideal, and here we solve this problem by introducing an algebra
-- transformer `upCache` that automatically caches the up-operations at tail positions
-- and invokes @downTail@ automatically. In this way, the meta-programs don't need to be
-- modified at all while obtaining the desired generated code.

-- | The monad @CacheT m n@ is basically the same as @n a@, except that @CacheT m n@ may
-- internally remember that some computations come from upping a piece of @m@-code (so that
-- later downing @CacheT m n@ can directly use that piece of code).
newtype CacheT m n a = CacheT { unCacheT :: n (CacheS m n a) }

-- | The constructor `Hit` means that it is a computation @n (Up a)@ coming from upping
-- a piece of code @Up (m a)@. The reason that we store both @Up (m a)@ and @n (Up a)@
-- is that we are only interested in caching up-operations in tail positions, so when an
-- an up-operation is no longer at the tail position after a @(>>=)@, we want to turn
-- it back into a normal @n@-computation.
data CacheS m n a where
  Hit :: Up (m a) -> n (Up a) -> CacheS m n (Up a)
  Mis :: a -> CacheS m n a

-- | The up-operation on @CacheT m n@ remembers the original @m@-program.
-- Note that we are only interested in remembering `UpOpId`. If there is a
-- continuation after the up, even if a pure continuation, it's better
-- to do a real up.
upCache :: forall m . AlgTrans '[UpOp m] '[UpOp m] '[CacheT m] Monad
upCache = algTrans1 $ \oalg -> \case
  Alg (UpOpId p)  -> CacheT (return (Hit p (upM oalg p)))
  Alg (UpOp_ p k) -> CacheT (upM oalg p >>= return . Mis . k)

-- | We can convert between `CacheT m n a` and `n a` by forgetting the cached up-operations.
-- This is of course not really an isomorphism but here we borrow `Iso` to organise the code
-- more cleanly.
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

  -- | We are only interested in caching up-operations at tail positions, so after
  -- a bind `Hit` becomes `Mis`.
  CacheT n >>= k = CacheT $
    n >>= \case
      Mis a     -> unCacheT (k a)
      Hit _ n'  -> n' >>= unCacheT . k

instance MonadTrans (CacheT m) where
  lift = Iso.bwd cacheConversion

instance Functor sig => Forward (Scp sig) (CacheT m) where
  fwd alg op = Iso.bwd cacheConversion (alg (hmap (Iso.fwd cacheConversion) op))
  -- Note that the following is wrong
  --
  -- > fwd alg (Scp op) = CacheT (alg (Scp (fmap unCacheT op)))
  --
  -- because the scoped operation is only applied to the @n@ part while semantically
  -- it should apply to both the @n@-part and also the cached computation.

instance Functor sig => Forward (Distr sig) (CacheT m) where
  fwd alg op = Iso.bwd cacheConversion (alg (hmap (Iso.fwd cacheConversion) op))

instance (Functor n, Monad m, n $~>> m) => CacheT m n $~> m where
  down (CacheT n) = downTail $ n <&> \case
    Mis a    -> Left a
    Hit c _  -> Right c

instance (Functor n, Monad n, Monad m, n $~>> m) => CacheT m n $~>> m where
  downTail (CacheT n) = downTail $ n <&> \case
    Mis (Left a)  -> Left a
    Mis (Right b) -> Right b
    -- Hit is impossible here