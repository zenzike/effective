{-|
Module      : Control.Effect.Internal.Handler
Description : Handlers and handler combinators
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Control.Effect.Internal.Handler where

import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.AlgTrans as LL hiding (weaken)
import Control.Effect.Internal.Runner as LL
import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Effs.Sum
import Control.Effect.Internal.Forward

import Data.Kind
import Data.List.Kind
import Data.Functor.Identity
import Data.HFunctor
import Data.Proxy

-- | A t'Handler' will process input effects @effs@ and produce output effects
-- @oeffs@, while working with a list of monad transformers @ts@. The final value
-- will be wrapped with @fs@.

type Handler
  :: [Effect]                             -- ^ effs  : input effects
  -> [Effect]                             -- ^ oeffs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ^ ts    : a list of carrier transformers
  -> Type                                 -- ^ a     : input type
  -> Type                                 -- ^ b     : output type
  -> Type

data Handler effs oeffs ts a b =
  Handler
  { -- | Given @oeffs@-effects on any monad @m@, running the monad transformer stack
    -- @ts m x@ into @m (fs x)@.
    hrun :: Runner oeffs ts a b Monad

    -- | Transforming @oeffs@-effects on any monad @m@ to @effs@-effects on @ts m@.
  , halg :: AlgTrans effs oeffs ts Monad
  }


-- * Building handlers

-- | A wrapper of the @Handler@ constructor.
{-# INLINE handler #-}
handler
  :: forall effs oeffs ts a b .
     (forall m . Monad m => Algebra oeffs m -> Apply ts m a -> m b)
  -> (forall m . Monad m => Algebra oeffs m -> Algebra effs (Apply ts m))
  -> Handler effs oeffs ts a b
handler run alg = Handler (Runner run) (AlgTrans alg)

-- | Given @hrun@ and @halg@ will construct a @Handler effs oeffs ts fs@. This
-- is a simplified version of the @Handler@ constructor where @run@ does
-- not need to be a modular runner.
{-# INLINE handler' #-}
handler'
  :: (forall m . Monad m => Apply ts m a -> m b)
  -> (forall m . Monad m => Algebra oeffs m -> Algebra effs (Apply ts m))
  -> Handler effs oeffs ts a b
handler' run alg = Handler (Runner (\_ -> run)) (AlgTrans (\oalg -> alg oalg))

runner
  :: forall ts a b. (forall m . Monad m => Apply ts m a -> m b)
  -> Handler '[] '[] ts a b
runner run = Handler (Runner (\_ -> run)) (AlgTrans (const absurdEffs))

infixr #:

(#:) :: forall effs oeffs effs' oeffs' ts a b . UnionAT# effs effs' oeffs oeffs'
      => AlgTrans effs oeffs ts Monad
      -> Handler effs' oeffs' ts a b -> Handler (effs `Union` effs') (oeffs `Union` oeffs') ts a b
algs #: Handler hrun halg = Handler (weakenREffs hrun) (weakenC (algs `unionAT` halg))

-- | The identity handler that doesn't transform the effects.
{-# INLINE identity #-}
identity :: Handler effs effs '[] a a
identity = Handler LL.idRunner LL.idAT

type Comp# effs1 ts1 ts2 =
  ( CompRunner# ts1 ts2
  , CompAT# ts1 ts2 effs1 Monad)

-- | Composing two handlers.
{-# INLINE comp #-}
comp :: ( forall m. Monad m => MonadApply ts1 m
        , forall m. Monad m => MonadApply ts2 m
        , Comp# effs1 ts1 ts2 )
     => Handler effs1 effs2 ts1 a1 a2
     -> Handler effs2 effs3 ts2 a2 a3
     -> Handler effs1 effs3 (ts1 :++ ts2) a1 a3
comp (Handler r1 a1) (Handler r2 a2) =
  Handler (weakenRC (compRunner a2 r1 r2)) (weakenC (compAT a1 a2))

-- | Weakens a handler from @Handler effs oeffs ts fs@ to @Handler effs' oeffs' ts fs@,
-- when @effs'@ injects into @effs@ and @oeffs@ injects into @oeffs'@.
{-# INLINE weaken #-}
weaken
  :: forall effs effs' oeffs oeffs' ts a b
  . ( Injects effs' effs , Injects oeffs oeffs')
  => Handler effs  oeffs  ts a b
  -> Handler effs' oeffs' ts a b
weaken (Handler run halg)
  = Handler (weakenR @_ @oeffs' run) (weakenEffs halg)

type Hide# heffs effs oeffs = (Injects (effs :\\ heffs) effs, Injects oeffs oeffs)

-- | Hides the effects in @heffs@ from the handler. The type argument @heffs@
-- must be given explicitly since it is only mentioned inside a non-injective
-- type family `:\\`.
{-# INLINE hide #-}
hide
  :: forall heffs effs oeffs ts a b
  . Hide# heffs effs oeffs
  => Proxy heffs
  -> Handler effs oeffs ts a b
  -> Handler (effs :\\ heffs) oeffs ts a b
hide _ h = weaken h

type Bypass# beffs effs oeffs =
  ( Append effs (beffs :\\ effs)
  , Injects (beffs :\\ effs) beffs
  , Injects beffs beffs
  , Injects effs effs
  , Injects oeffs (oeffs `Union` beffs)
  , Injects beffs (oeffs `Union` beffs) )

-- | Operations from the output effect @oeffs@ of a handler can be added
-- to the input effect if the handler can forward it.
{-# INLINE bypass #-}
bypass
  :: forall beffs effs oeffs ts a b
  . ( ForwardsM beffs ts
    , Bypass# beffs effs oeffs )
  => Proxy beffs
  -> Handler effs oeffs ts a b
  -> Handler (effs `Union` beffs) (oeffs `Union` beffs) ts a b
bypass _ (Handler run alg) = Handler (weakenR run) (LL.withFwds (Proxy @beffs) alg)

-- | An algebra transformer that doesn't transform the carrier can be
-- regarded as a handler trivially.
{-# INLINE fromAT #-}
fromAT :: AlgTrans effs oeffs '[] Monad -> Handler effs oeffs '[] a a
fromAT at = handler (\_ -> id) (getAT at)

-- | Interpret @effs@-effects using @oeffs@-effects without transforming the carrier.
-- This is done by using the supplied @rephrase :: Effs effs m x -> Prog oeffs x@
-- parameter to translate @effs@ into a program that uses @oeffs@.
--
-- The function `interpret` is most useful for algebraic operations. For other families
-- of operations, `interpretM` is more useful.
{-# INLINE interpret #-}
interpret
  :: forall effs oeffs a
  .  ( HFunctor (Effs effs), HFunctor (Effs oeffs) )
  => (forall m x . Effs effs m x -> Prog oeffs x)   -- ^ @rephrase@
  -> Handler effs oeffs '[] a a
interpret = fromAT . interpretAT

-- | Interpret @effs@-effects using @oeffs@-effects without transforming the carrier.
-- This is done by using the supplied @rephrase :: Effs effs m x -> Prog oeffs x@
-- parameter to translate @effs@ into a program that uses @oeffs@.
{-# INLINE interpretAT #-}
interpretAT
  :: forall effs oeffs
  .  ( HFunctor (Effs effs), HFunctor (Effs oeffs) )
  => (forall m x . Effs effs m x -> Prog oeffs x)   -- ^ @rephrase@
  -> AlgTrans effs oeffs '[] Monad
interpretAT rephrase = AlgTrans (\oalg op -> eval oalg (rephrase op))

{-# INLINE interpret1 #-}
-- | A special case of `interpret` for one effect @eff@.
interpret1
  :: forall eff oeffs a
  .  ( HFunctor eff, HFunctor (Effs oeffs) )
  => (forall m x . eff m x -> Prog oeffs x)
  -> Handler '[eff] oeffs '[] a a
interpret1 rephrase = interpret (\(Eff e) -> rephrase e)

{-# INLINE interpretAT1 #-}
-- | A special case of `interpretAT` for one effect @eff@.
interpretAT1
  :: forall eff oeffs
  .  ( HFunctor eff, HFunctor (Effs oeffs) )
  => (forall m x . eff m x -> Prog oeffs x)
  -> AlgTrans '[eff] oeffs '[] Monad
interpretAT1 rephrase = interpretAT (\(Eff e) -> rephrase e)

{-# INLINE interpretM #-}
-- | A generalisation of `interpret` for non-algebraic operations.
-- The result of @interpretM mrephrase@ is a new @Handler effs oeffs '[] '[]@.
-- This is created by using the supplied @mrephrase :: (forall x . Effs oeffs m x -> m x) -> Effs effs m x -> m x@ parameter.
-- to rephrase @effs@ into an arbitrary monad @m@.
-- When @mrephrase@ is used, it is given an @oalg :: Effs oeffs m x -> m x@
-- parameter that makes it possible to create a value in @m@.
interpretM
  :: forall effs oeffs a .
     (forall m . Monad m => (forall x . Effs oeffs m x -> m x)
                         -> (forall x . Effs effs m x -> m x))   -- ^ @mrephrase@
  -> Handler effs oeffs '[] a a
interpretM mrephrase
  = handler @effs @oeffs @'[] (const id) mrephrase

{-# INLINE interpretM1 #-}
interpretM1
  :: forall eff oeffs a.
     (forall m . Monad m => (forall x . Effs oeffs m x -> m x)
                         -> (forall x . eff m x -> m x))   -- ^ @mrephrase@
  -> Handler '[eff] oeffs '[] a a
interpretM1 mrephrase
  = handler @'[eff] @oeffs @'[] (const id) (\oalg (Eff op) -> mrephrase oalg op)

-- | Case splitting on the union of two effect rows. Note that `Union` is defined
-- two be @effs1 ++ (effs2 :\\ effs1)@, so if an effect @e@ is both a member of @effs1@
-- and @effs2@, it is consumed by the first handler.
{-# INLINE caseHdl #-}
caseHdl :: forall effs1 effs2 oeffs ts a1 a2 a3 a4.
          CaseTrans# effs1 effs2
       =>  Handler effs1 oeffs ts a1 a2
       ->  Handler effs2 oeffs ts a3 a4
       -> Handler (effs1 `Union` effs2) oeffs ts a1 a2
caseHdl (Handler r1 a1) (Handler _ a2) = Handler r1 (caseATSameC a1 a2)

{-# INLINE unionHdl #-}
-- | Case splitting on the union of two effect rows, and the two handlers may output
-- different effects.
unionHdl :: forall effs1 effs2 oeffs1 oeffs2 ts a1 a2 a3 a4.
          UnionAT# effs1 effs2 oeffs1 oeffs2
       =>  Handler effs1 oeffs1 ts a1 a2
       ->  Handler effs2 oeffs2 ts a3 a4
       -> Handler (effs1 `Union` effs2) (oeffs1 `Union` oeffs2) ts a1 a2
unionHdl (Handler r1 a1) (Handler _ a2) = Handler (weakenR r1) (weakenC (unionAT a1 a2))

{-# INLINE appendHdl #-}
-- | Case splitting on the append of two effect rows, and the two handlers may output
-- different effects.
appendHdl :: forall effs1 effs2 oeffs1 oeffs2 ts a1 a2 a3 a4.
          AppendAT# effs1 effs2 oeffs1 oeffs2
       =>  Handler effs1 oeffs1 ts a1 a2
       ->  Handler effs2 oeffs2 ts a3 a4
       -> Handler (effs1 :++ effs2) (oeffs1 :++ oeffs2) ts a1 a2
appendHdl (Handler r1 a1) (Handler _ a2) = Handler (weakenR r1) (weakenC (appendAT a1 a2))

-- * Fusion-based handler combinators

infixr 9 `fuse`, |>

{-# INLINE fuse #-}
{-# INLINE (|>) #-}
fuse, (|>)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3
  . ( forall m . Monad m => MonadApply ts1 m
    , forall m . Monad m => MonadApply ts2 m
    , ForwardsM effs2 ts1
    , ForwardsM (oeffs1 :\\ effs2) ts2
    , LL.FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2
    , LL.FuseR# effs2 oeffs1 oeffs2 ts1 ts2
    )
  => Handler effs1 oeffs1 ts1 a1 a2   -- ^ @h1@
  -> Handler effs2 oeffs2 ts2 a2 a3   -- ^ @h2@
  -> Handler (effs1 `Union` effs2)
             ((oeffs1 :\\ effs2) `Union` oeffs2)
             (ts1 :++ ts2)
             a1 a3
-- | Fusing handlers `h1 :: Handler effs1 oeffs1 ts1 fs1` and `h2 :: Handler effs2
-- oeffs2 ts2 fs2` results in a handler with the composed transformer stack @ts1 :++ ts2@
-- that can deal with the effects of `effs1` and those of `effs2`, as well as deal
-- with the effects @oeffs1@ produced by @h1@ using @h2@ appropriately. More
-- precisely, if a member of @oeffs1@ is in `effs2`, then it is consumed by `h2`;
-- if it is not in `effs2`, it can only be re-produced by the fused handler and in
-- this case they have to be forwardable by @ts2@.
--
-- Moreover, the effects @effs2@ are handled by @h2@ so they must be forwardable by @ts1@.
fuse (Handler run1 malg1) (Handler run2 malg2)
  = Handler (weakenRC (LL.fuseR malg2 run1 run2)) (weakenC (LL.fuseAT malg1 malg2))

-- | A synonym for `fuse`.
(|>) = fuse


infixr 9 `pipe`, ||>

{-# INLINE pipe #-}
{-# INLINE (||>) #-}

pipe, (||>)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3
  . ( forall m . Monad m => MonadApply ts1 m
    , forall m . Monad m => MonadApply ts2 m
    , LL.PipeAT# effs2 oeffs1 oeffs2 ts1 ts2
    , LL.FuseR# effs2 oeffs1 oeffs2 ts1 ts2
    , ForwardsM (oeffs1 :\\ effs2) ts2
    )
  => Handler effs1 oeffs1 ts1 a1 a2 -- ^ Handler @h1@
  -> Handler effs2 oeffs2 ts2 a2 a3    -- ^ Handler @h2@
  -> Handler effs1
             ((oeffs1 :\\ effs2) `Union` oeffs2)
             (ts1 :++ ts2)
             a1 a3
-- Piping two handlers @h1@ and @h2@ is a relaxed version of composing two
-- handlers (`comp`). The output effects of @h1@ doesn't have to exactly match the
-- input effects of @h2@ (as required by `comp`). Instead, if an output effect
-- produced by @h1@ is not handled by @h2@, it will be re-produced by @pipe h1 h2@.
pipe (Handler run1 malg1)  (Handler run2 malg2)
  = Handler (LL.weakenRC (LL.fuseR malg2 run1 run2)) (LL.weakenC (LL.pipeAT malg1 malg2))

-- | A synonym for 'pipe'
(||>) = pipe


type Pass# effs1 effs2 oeffs1 oeffs2 ts1 ts2 =
  ( PassAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 Monad
  , FuseR# effs2 oeffs1 oeffs2 ts1 ts2
  , Injects (oeffs1 `Union` oeffs2) (oeffs1 `Union` oeffs2))

-- | @pass h1 h2@ results in a handler that recognises all the effects recognised by
-- @h1@ and @h2@, but unlike @fuse h1 h2@, @pass@ doesn't use @h2@ to intercept the
-- effects produced by @h1@.
pass :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
        ( forall m. Monad m => MonadApply ts2 m
        , ForwardsM  effs2 ts1
        , ForwardsM oeffs1 ts2
        , Pass# effs1 effs2 oeffs1 oeffs2 ts1 ts2)
     => Handler effs1 oeffs1 ts1 a1 a2         -- ^ Handler @h1@
     -> Handler effs2 oeffs2 ts2 a2 a3         -- ^ Handler @h2@
     -> Handler (effs1 `Union` effs2)
                (oeffs1 `Union` oeffs2)
                (ts1 :++ ts2)
                a1 a3
pass (Handler r1 a1) (Handler r2 a2)
  = Handler (LL.weakenR (LL.passR a2 r1 r2)) (LL.weakenC (LL.passAT a1 a2))

{-# INLINE generalFuse #-}
-- | `generalFuse` subsumes @fuse@, @pass@, and @pipe@ by having two type arguments
-- @feffs@ and @ieffs@ such that
--   1. @feffs@ is a subset of @effs2@ and it specifies the effects that we want to be
--      forwarded along @ts1@ and exposed by the resulting handler;
--   2. @ieffs@ is a subset of @effs2@ and it specifies the effects that we want to
--      use to intercept the effects produced by @h1@.
-- Therefore @generalFuse@ instantiates to
--   1. `fuse` with @feffs ~ effs2@ and @ieffs ~ effs2@,
--   2. `pipe` with @feffs ~ []@    and @ieffs ~ effs2@,
--   3. `pass` with @feffs ~ effs2@ and @ieffs ~ []@.
-- (When both @feffs@ and @ieffs@ are empty, @generalFuse@ becomes useless so there
-- isn't this case defined specially.)
generalFuse
  :: forall feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
     ( forall m . Monad m => MonadApply ts1 m
     , forall m . Monad m => MonadApply ts2 m
     , Injects feffs effs2
     , Injects ieffs effs2
     , ForwardsM feffs ts1
     , ForwardsM (oeffs1 :\\ ieffs) ts2
     , GeneralFuseAT# feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2
     , LL.FuseR# effs2 oeffs1 oeffs2 ts1 ts2
     , Injects oeffs2 oeffs2
     )
  => Proxy feffs -> Proxy ieffs
  -> Handler effs1 oeffs1 ts1 a1 a2
  -> Handler effs2 oeffs2 ts2 a2 a3
  -> Handler (effs1 `Union` feffs)
             ((oeffs1 :\\ ieffs) `Union` oeffs2)
             (ts1 :++ ts2)
             a1 a3
generalFuse p1 p2 (Handler r1 a1) (Handler r2 a2)
  = Handler (LL.weakenRC (LL.fuseR (weakenIEffs @ieffs a2) r1 r2))
            (LL.weakenC (LL.generalFuseAT p1 p2 a1 a2))

recall
  :: forall reffs effs oeffs ts a b .
     ( Append reffs (effs :\\ reffs)
     , Injects oeffs (reffs `Union` oeffs)
     , Injects reffs (reffs `Union` oeffs)
     , Injects reffs effs
     , Injects (effs :\\ reffs) effs
     , ForwardsM reffs ts
     , forall m . Monad m => MonadApply ts m
     )
  => Proxy reffs -> Handler effs oeffs ts a b
  -> Handler (reffs `Union` effs) (reffs `Union` oeffs) ts a b
recall _ (Handler run halg) =
  Handler (weakenR @_ @(reffs `Union` oeffs) run)
          (AlgTrans $ \(oalg :: Algebra (reffs `Union` oeffs) m) ->
              heither @reffs @(effs :\\ reffs)
                -- sticky branch: consume via h, then recall downstream
                (\opR -> do
                    r <- getAT halg (weakenAlg @oeffs oalg) (injs @reffs @effs opR)
                    _ <- getAT (fwds @reffs @ts) (weakenAlg @reffs oalg) opR
                    pure r)
                -- non-sticky: just delegate to h
                (\opE -> getAT halg (weakenAlg @oeffs oalg)
                                 (injs @(effs :\\ reffs) @effs opE)))


-- * Using handlers

-- | @handle h p@ uses the handler @h@ to evaluate the program @p@. All of the
-- effects @effs@ in the program must be recognised by the handler,
-- and the handler must produce no effects.

{-# INLINE handle #-}
handle :: forall effs ts fs a b .
  (Monad (Apply ts Identity), HFunctor (Effs effs))
  => Handler effs '[] ts a b      -- ^ Handler @h@ with no output effects
  -> Prog effs a                  -- ^ Program @p@ with effects @effs@
  -> b
handle (Handler run halg)
  = runIdentity . LL.getR run absurdEffs . eval (getAT halg (absurdEffs @Identity))

type HandleM# effs xeffs =
  ( Injects (xeffs :\\ effs) xeffs
  , Append effs (xeffs :\\ effs)
  , HFunctor (Effs (effs `Union` xeffs)))

-- | @handleM xalg h p@ uses the handler @h@ to evaluate the program @p@ into some
-- monad @m@ (e.g. the @IO@ monad). The monad @m@ may come with some effects @xeffs@
-- and the program can make use of these effects, in addition to the effects @effs@
-- handled by the handler @h@. The effects @xeffs@ on @m@ must be forwardable by
-- the transformer stack @ts@.
-- (When an effect is both in @effs@ and @xeffs@, it is handled by @h@).
handleM :: forall effs oeffs xeffs m ts fs a b .
  ( Monad m
  , Monad (Apply ts m)
  , ForwardsM xeffs ts
  , Injects oeffs xeffs
  , HandleM# effs xeffs
  )
  => Algebra xeffs m                 -- ^ Algebra @xalg@ for external effects @xeffs@
  -> Handler effs oeffs ts a b       -- ^ Handler @h@
  -> Prog (effs `Union` xeffs) a     -- ^ Program @p@ that contains @xeffs@
  -> m b
handleM xalg (Handler run halg)
  = getR run @m (xalg . injs)
  . eval (hunion @effs @xeffs (getAT halg (xalg . injs)) (getAT (fwds @_ @ts) xalg))

-- | A variant of @handleM@ where the program doesn't explictly use the effect
-- @xeffs@ on the monad @m@, but may output some effects @oeffs@ ⊆ @xeffs@. Therefore
-- the transformer stack @ts@ doesn't have to forward the effects @xeffs@.
handleM' :: forall effs oeffs xeffs m ts a b .
  ( Monad m
  , Monad (Apply ts m)
  , Injects oeffs xeffs
  , HFunctor (Effs effs) )
  => Algebra xeffs m                 -- ^ Algebra @xalg@ for external effects @xeffs@
  -> Handler effs oeffs ts a b       -- ^ Handler @h@
  -> Prog effs a
  -> m b
handleM' xalg (Handler run halg)
  = getR run @m (xalg . injs) . eval (getAT halg (xalg . injs))

-- | `handleMFwds` is a middle ground between `handleM` and `handleM'`: a type argument
-- @yeffs@ is given explicitly to specify the subset of @xeffs@ that the program really
-- needs (and must be forwardable by @ts@).
handleMFwds :: forall yeffs effs oeffs xeffs m ts a b .
  ( Monad m
  , Monad (Apply ts m)
  , Injects oeffs xeffs
  , Injects yeffs xeffs
  , ForwardsM yeffs ts
  , HandleM# effs yeffs )
  => Proxy yeffs                     -- ^ @yeffs@ can't be infered so must be given explicitly
  -> Algebra xeffs m                 -- ^ Algebra @xalg@ for external effects @xeffs@
  -> Handler effs oeffs ts a b        -- ^ Handler @h@
  -> Prog (effs `Union` yeffs) a
  -> m b
handleMFwds _ xalg (Handler run halg)
  = getR run @m (xalg . injs)
  . eval (hunion @effs @yeffs (getAT halg (xalg . injs))
                              (getAT (fwds @_ @ts) (xalg . injs)))

type HandleP# effs xeffs =
  ( HandleM# effs xeffs
  , HFunctor (Effs xeffs)
  , Monad (Prog xeffs) )

-- | @handleP h p@ uses the handler @h@ to evaluate the program @p@, resulting
-- in a program with effects @xeffs@ that are not recognised by @h@.
-- If an effect is both in @effs@ and @xeffs@, it is handled by @h@.
handleP :: forall effs oeffs xeffs ts fs a b .
  ( Monad (Apply ts (Prog xeffs))
  , ForwardsM xeffs ts
  , Injects oeffs xeffs
  , HandleP# effs xeffs )
  => Handler effs oeffs ts a b        -- ^ Handler @h@
  -> Prog (effs `Union` xeffs) a     -- ^ Program @p@ that contains @xeffs@
  -> Prog xeffs b
handleP = handleM progAlg

-- | A variant of @handleP'@ where the program only uses the effects provided
-- by the handler @h@.
handleP' :: forall effs oeffs xeffs ts fs a b .
  ( Monad (Apply ts (Prog xeffs))
  , Forwards xeffs ts
  , Injects oeffs xeffs
  , HFunctor (Effs effs)
  , HFunctor (Effs xeffs) )
  => Handler effs oeffs ts a b       -- ^ Handler @h@
  -> Prog effs a                     -- ^ Program @p@ that contains @xeffs@
  -> Prog xeffs b

handleP' = handleM' progAlg


type HandleMApp# effs xeffs =
  ( HFunctor (Effs (effs :++ xeffs))
  , Append effs xeffs )

-- | @handleMApp xalg h p@ is a variant of `handleM` where @effs `Union` xeffs@ is replaced
-- by '(:++)'.
-- In most cases, you should just use `handleM` but sometimes limitations regarding class
-- constraints in GHC necessitate the use of @handleMApp@ (for example, in `Control.Effect.HOStore.Safe.handleHSM`.)

handleMApp :: forall effs oeffs xeffs m ts fs a b .
  ( Monad m
  , Monad (Apply ts m)
  , ForwardsM xeffs ts
  , Injects oeffs xeffs
  , HandleMApp# effs xeffs )
  => Algebra xeffs m                -- ^ Algebra @xalg@ for external effects @xeffs@
  -> Handler effs oeffs ts a b       -- ^ Handler @h@
  -> Prog (effs :++ xeffs) a        -- ^ Program @p@ that contains @xeffs@
  -> m b
handleMApp xalg (Handler run halg)
  = getR run @m (xalg . injs)
  . eval (heither @effs @xeffs (getAT halg (xalg . injs)) (getAT (fwds @_ @ts) xalg))

-- | @handleP' h p@ is a variant of `handleP` where @effs `Union` xeffs@ is replaced
-- by simply '(:++)'.
-- In most cases, you should just use `handleP` but sometimes limitations regarding class
-- constraints in GHC necessitate the use of @handleP'@ (for example, in `Control.Effect.HOStore.Safe.handleHSM`.)
handlePApp :: forall effs oeffs xeffs ts fs a b .
  ( ForwardsM xeffs ts
  , Monad (Apply ts (Prog xeffs))
  , Injects oeffs xeffs
  , HandleMApp# effs xeffs
  , HFunctor (Effs xeffs)
  ) => Handler effs oeffs ts a b        -- ^ Handler @h@
  -> Prog (effs :++ xeffs) a           -- ^ Program @p@ that contains @xeffs@
  -> Prog xeffs b
handlePApp = handleMApp progAlg