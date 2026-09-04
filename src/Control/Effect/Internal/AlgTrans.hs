{-|
Module      : Control.Effect.Internal.AlgTrans
Description : Transforming effectful operations along carrier transformers
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental

This module contains combinators of /algebra transformers/, the core data type
of this library.
-}
{-# LANGUAGE ImpredicativeTypes, QuantifiedConstraints, UndecidableInstances, AllowAmbiguousTypes #-}
{-# LANGUAGE MonoLocalBinds, LambdaCase, BlockArguments #-}
{-# LANGUAGE PartialTypeSignatures, MagicHash #-}

module Control.Effect.Internal.AlgTrans where

import Data.List.Kind
import Data.HFunctor ( HFunctor )
import Data.Proxy

import Control.Effect.Internal.Algebra
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Prog ( Prog, eval )
import Control.Effect.Internal.Forward

-- * Using algebra transformers and runners

-- | Evaluating a program with an algebra transformer.
{-# INLINE evalAT #-}
evalAT
  :: forall effs oeffs xeffs ts cs m a.
     ( cs m
     , Members oeffs xeffs
     , Monad (Apply ts m) )
  => Algebra xeffs m               -- ^ External effects on @m@
  -> AlgTrans effs oeffs ts cs     -- ^ Algebra transformer
  -> Prog effs a                   -- ^ Program to be handled
  -> Apply ts m a
evalAT oalg alg = eval (getAT alg (weakenAlg oalg))

-- | Evaluating a program with an algebra transformer that outputs no effects.
{-# INLINE evalAT' #-}
evalAT'
  :: forall m effs ts cs a.
     ( cs m
     , Monad (Apply ts m) )
  => AlgTrans effs '[] ts cs       -- ^ Algebra transformer producing no effects
  -> Prog effs a                   -- ^ Program to be handled
  -> Apply ts m a
evalAT' alg = eval (getAT alg (emptyAlg @m))

-- * Building algebra transformers

-- ** Primitive combinators

-- | Treating an algebra on @m@ as a trivial algebra transformer that only works
-- when the carrier is exactly @m@.
{-# INLINE asAT #-}
asAT :: forall effs m. Algebra effs m -> AlgTrans effs '[] '[] ((~) m)
asAT alg = AlgTrans \_ -> alg

-- | The identity algebra transformer.
{-# INLINE idAT #-}
idAT :: forall effs cs. AlgTrans effs effs '[] cs
idAT = AlgTrans \alg -> alg

-- | In this library, constraints with names ending with a hash will always be
-- satisfied automatically when the parameters are instantiated with concrete values.
-- Users don't need to care about them.
type CompAT# ts1 ts2 = ( forall m . Assoc ts1 ts2 m )

-- | Composing two algebra transformers.
{-# INLINE compAT #-}
compAT
  :: forall effs1 effs2 effs3 ts1 ts2 cs1 cs2.
     (CompAT# ts1 ts2)
  => AlgTrans effs1 effs2 ts1 cs1   -- ^ The first algebra transformer
  -> AlgTrans effs2 effs3 ts2 cs2   -- ^ The second algebra transformer
  -> AlgTrans effs1 effs3 (ts1 :++ ts2) (CompC ts2 cs1 cs2)
compAT alg1 alg2 = AlgTrans \(oalg :: Algebra effs3 m) -> getAT alg1 (getAT alg2 oalg)

-- | Every algebra transformer can be used as one that processes fewer input effects,
-- generating more output effects, and/or with stronger carrier constraints.
{-# INLINE weakenAT #-}
weakenAT
  :: forall effs' oeffs' cs' effs oeffs cs ts.
     ( Members effs' effs, Members oeffs oeffs', forall m. cs' m => cs m )
  => AlgTrans effs  oeffs  ts cs    -- ^ Algebra transformer to weaken
  -> AlgTrans effs' oeffs' ts cs'
weakenAT at = AlgTrans \oalg -> weakenAlg (getAT at (weakenAlg oalg))

type CaseTrans# effs1 effs2 =
  ( Members (effs2 :\\ effs1) effs2 )

-- | Case splitting on the union of two effect rows. Note that `Union` is defined
-- to be @effs1 ++ (effs2 :\\ effs1)@, so if an effect @e@ is both a member of @effs1@
-- and @effs2@, it is consumed by the first algebra transformer.
{-# INLINE caseAT #-}
caseAT
  :: forall effs1 effs2 cs1 cs2 oeffs ts.
     CaseTrans# effs1 effs2
  => AlgTrans effs1 oeffs ts cs1   -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs ts cs2   -- ^ The second algebra transformer
  -> AlgTrans (effs1 `Union` effs2) oeffs ts (AndC cs1 cs2)
caseAT at1 at2 = AlgTrans \oalg -> unionAlg (getAT at1 oalg) (getAT at2 oalg)

-- | Case splitting on the concatenation of two effect rows.
{-# INLINE caseAT' #-}
caseAT'
  :: forall effs1 effs2 cs1 cs2 oeffs ts.
     AlgTrans effs1 oeffs ts cs1   -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs ts cs2   -- ^ The second algebra transformer
  -> AlgTrans (effs1 :++ effs2) oeffs ts (AndC cs1 cs2)
caseAT' at1 at2 = AlgTrans \oalg -> appendAlg (getAT at1 oalg) (getAT at2 oalg)

-- ** Derived combinators of algebra transformers

-- | Algebra transformer for a single effect.
{-# INLINE algTrans1 #-}
algTrans1
  :: forall eff oeffs ts cs.
     (forall m. cs m => Algebra oeffs m -> forall x. eff (Apply ts m) x -> Apply ts m x) -- ^ Transformation for the single effect
  -> AlgTrans '[eff] oeffs ts cs
algTrans1 at = AlgTrans \(oalg :: Algebra oeffs m) -> at oalg :# emptyAlg

-- | Algebra transformer that doesn't need an output effect.
{-# INLINE algTrans' #-}
algTrans'
  :: forall effs oeffs ts cs.
     (forall m. cs m => Algebra effs (Apply ts m)) -- ^ Algebra for the input effects
  -> AlgTrans effs oeffs ts cs
algTrans' alg = AlgTrans (\(_ :: Algebra oeffs m) -> alg @m)

-- | Replace the carrier constraint of an algebra transformer with a stronger one.
{-# INLINE weakenCS #-}
weakenCS
  :: forall cs' cs effs oeffs ts.
     (forall m. cs' m => cs m)
  => AlgTrans effs oeffs ts cs     -- ^ Algebra transformer to weaken
  -> AlgTrans effs oeffs ts cs'
weakenCS at = AlgTrans $ getAT at

{-# INLINE weakenCSMonad #-}
-- | Drop a @'CompC' ts2 Monad Monad@ carrier constraint down to plain @Monad@.
--
-- The algebra-transformer counterpart of 'Control.Effect.Internal.Runner.weakenRCSMonad':
-- the @cs = 'CompC' ts2 Monad Monad@, @cs' = Monad@ specialisation of 'weakenCS'.
-- See that function for why this wrapper is needed on GHC 9.14.
weakenCSMonad
  :: forall ts2 effs oeffs ts.
     (forall m. Monad m => MonadApply ts2 m)
  => AlgTrans effs oeffs ts (CompC ts2 Monad Monad) -- ^ Algebra transformer to weaken
  -> AlgTrans effs oeffs ts Monad
weakenCSMonad = weakenCS

-- | Replace the carrier constraint @cs@ of an algebra transformer with the conjunction
-- of @cs@ and another constraint @cs'@.
{-# INLINE weakenCSAnd #-}
weakenCSAnd
  :: forall cs' cs effs oeffs ts.
     AlgTrans effs oeffs ts cs     -- ^ Algebra transformer
  -> AlgTrans effs oeffs ts (AndC cs cs')
weakenCSAnd at = AlgTrans $ getAT at

-- | Forget some input effects and add some unused output effects.
{-# INLINE weakenEffs #-}
weakenEffs
  :: ( Members effs' effs, Members oeffs oeffs' )
  => AlgTrans effs  oeffs  ts cs   -- ^ Algebra transformer to weaken
  -> AlgTrans effs' oeffs' ts cs
weakenEffs = weakenAT

-- | Add some unused output effects.
{-# INLINE weakenOEffs #-}
weakenOEffs
  :: forall oeffs' oeffs effs ts cs.
     Members oeffs oeffs'
  => AlgTrans effs oeffs  ts cs    -- ^ Algebra transformer to weaken
  -> AlgTrans effs oeffs' ts cs
weakenOEffs at = AlgTrans \ oalg -> getAT at (weakenAlg oalg)

-- | Forget some input effects of an algebra transformer.
{-# INLINE weakenIEffs #-}
weakenIEffs
  :: forall effs' effs oeffs ts cs.
     Members effs' effs
  => AlgTrans effs  oeffs ts cs    -- ^ Algebra transformer to weaken
  -> AlgTrans effs' oeffs ts cs
weakenIEffs at = AlgTrans \ oalg -> weakenAlg (getAT at oalg)


-- | Interpret @effs@-effects using @oeffs@-effects without transforming the carrier.
-- This is done by using the supplied @rephrase@
-- parameter to translate @effs@ into a program that uses @oeffs@.
{-# INLINE interpretAT #-}
interpretAT
  :: forall effs oeffs.
     (forall m x . Case effs m x (Prog oeffs x))                -- ^ @rephrase@
  -> AlgTrans effs oeffs '[] Monad
interpretAT rephrase = AlgTrans (\oalg -> algebraFromCase (fmap (eval oalg) rephrase))

{-# INLINE interpretAT1 #-}
-- | A special case of `interpretAT` for one effect @eff@.
interpretAT1
  :: forall eff oeffs.
     (forall m x. eff m x -> Prog oeffs x) -- ^ Effect rephrasing function
  -> AlgTrans '[eff] oeffs '[] Monad
interpretAT1 rephrase = AlgTrans (\oalg -> singAlg (eval oalg . rephrase))

type HideAT# effs effs' = (Members (effs :\\ effs') effs)

-- | Forget some input effects @effs'@.
{-# INLINE hideAT #-}
hideAT
  :: forall effs' effs oeffs ts cs.
     HideAT# effs effs'
  => AlgTrans effs  oeffs ts cs    -- ^ Algebra transformer to hide effects from
  -> AlgTrans (effs :\\ effs') oeffs ts cs
hideAT at = AlgTrans \ oalg -> weakenAlg (getAT at oalg)

-- | Case splitting with the same carrier constraint.
{-# INLINE caseATsameCS #-}
caseATsameCS
  :: forall effs1 effs2 cs oeffs ts.
     CaseTrans# effs1 effs2
  => AlgTrans effs1 oeffs ts cs                    -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs ts cs                    -- ^ The second algebra transformer
  -> AlgTrans (effs1 `Union` effs2) oeffs ts cs
caseATsameCS at1 at2 = weakenCS (caseAT at1 at2)

-- | Case splitting with the same carrier constraint.
{-# INLINE caseATsameCS' #-}
caseATsameCS'
  :: forall effs1 effs2 cs oeffs ts.
     AlgTrans effs1 oeffs ts cs                    -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs ts cs                    -- ^ The second algebra transformer
  -> AlgTrans (effs1 :++ effs2) oeffs ts cs
caseATsameCS' at1 at2 = weakenCS (caseAT' at1 at2)

type UnionAT# effs1 effs2 oeffs1 oeffs2 =
  ( Members effs1 effs1, Members effs2 effs2
  , Members oeffs1 (oeffs1 `Union` oeffs2)
  , Members oeffs2 (oeffs1 `Union` oeffs2)
  , CaseTrans# effs1 effs2)

-- | The most general form of case splitting on the union of input effects.
unionAT
  :: forall effs1 effs2 oeffs1 oeffs2 cs1 cs2 ts.
     UnionAT# effs1 effs2 oeffs1 oeffs2
  => AlgTrans effs1 oeffs1 ts cs1                              -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs2 ts cs2                              -- ^ The second algebra transformer
  -> AlgTrans (effs1 `Union` effs2) (oeffs1 `Union` oeffs2) ts (AndC cs1 cs2)
unionAT at1 at2 = caseAT (weakenAT @effs1 at1) (weakenAT @effs2 at2)

type AppendAT# effs1 effs2 oeffs1 oeffs2 =
  ( Members effs1 effs1, Members effs2 effs2
  , Members oeffs1 (oeffs1 :++ oeffs2)
  , Members oeffs2 (oeffs1 :++ oeffs2)
  )

-- | The most general form of case splitting on the concatenation of input effects.
appendAT
  :: forall effs1 effs2 oeffs1 oeffs2 cs1 cs2 ts.
     AppendAT# effs1 effs2 oeffs1 oeffs2
  => AlgTrans effs1 oeffs1 ts cs1                          -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs2 ts cs2                          -- ^ The second algebra transformer
  -> AlgTrans (effs1 :++ effs2) (oeffs1 :++ oeffs2) ts (AndC cs1 cs2)
appendAT at1 at2 = caseAT' (weakenAT @effs1 at1) (weakenAT @effs2 at2)

type WithFwds# effs oeffs xeffs =
  ( CaseTrans# effs xeffs
  , Members xeffs xeffs
  , Members effs effs
  , Members oeffs (oeffs `Union` xeffs)
  , Members xeffs (oeffs `Union` xeffs) )

-- | Bypassing some forwardable effects @feffs@ along an algebra transformer.
-- Members of @feffs@ that are already in @effs@ or @oeffs@ are ignored.
{-# INLINE withFwdsAT #-}
withFwdsAT
  :: forall feffs effs oeffs ts cs.
     ( ForwardsC cs feffs ts
     , WithFwds# effs oeffs feffs )
  => Proxy feffs                  -- ^ The effects to be forwarded
  -> AlgTrans effs oeffs ts cs    -- ^ An algebra transformer that can forward @feffs@
  -> AlgTrans (effs `Union` feffs) (oeffs `Union` feffs) ts cs
withFwdsAT _ at = weakenCS (unionAT at (fwds @feffs))

type WithFwds'# effs oeffs xeffs =
  ( Members xeffs xeffs
  , Members effs effs
  , Members oeffs (oeffs :++ xeffs)
  , Members xeffs (oeffs :++ xeffs) )

-- | Bypassing forwardable effects along an algebra transformer.
{-# INLINE withFwdsAT' #-}
withFwdsAT'
  :: forall feffs effs oeffs ts cs.
     ( ForwardsC cs feffs ts
     , WithFwds'# effs oeffs feffs )
  => Proxy feffs                                      -- ^ Effects to be forwarded
  -> AlgTrans effs oeffs ts cs                        -- ^ Algebra transformer
  -> AlgTrans (effs :++ feffs) (oeffs :++ feffs) ts cs
withFwdsAT' _ at = weakenCS (appendAT at (fwds @feffs))

-- ** Fusion-based combinators
type FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 =
   ( GeneralFuseAT# effs2 effs2 effs1 effs2 oeffs1 oeffs2 ts1 ts2
   , Members effs2 effs2 )

infixr 9 `fuseAT`, `fuseAT'`

-- | @fuseAT at1 at2@ composes @at1@ and @at2@ in a way that uses @at2@ maximally:
--    1. all the input effects @effs2@ of @at2@ are visible in the input effects of the final result, and
--    2. the output effects @oeffs1@ of @at1@ are intercepted by @effs2@ as much as possible.
{-# INLINE fuseAT #-}
fuseAT
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2
  => ( ForwardsC cs1 effs2 ts1, ForwardsC cs2 (oeffs1 :\\ effs2) ts2 )
  => AlgTrans effs1 oeffs1 ts1 cs1
     -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs2 ts2 cs2
     -- ^ The second algebra transformer
  -> AlgTrans (effs1 `Union` effs2)
              ((oeffs1 :\\ effs2) `Union` oeffs2)
              (ts1 :++ ts2)
              (CompC ts2 cs1 cs2)
fuseAT at1 at2 = generalFuseAT (Proxy @effs2) (Proxy @effs2) at1 at2

-- | A variant of `fuseAT` that demands the carrier constraint @cs1@ of the
-- first algebra transformer is always satisfied by @Apply ts2 m@ whenever @cs2 m@
-- holds. This is useful for keeping the constraints simple.
{-# INLINE fuseAT' #-}
fuseAT'
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2
  => ( ForwardsC cs1 effs2 ts1, ForwardsC cs2 (oeffs1 :\\ effs2) ts2,
       forall m. cs2 m => cs1 (Apply ts2 m) )
  => AlgTrans effs1 oeffs1 ts1 cs1
     -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs2 ts2 cs2
     -- ^ The second algebra transformer
  -> AlgTrans (effs1 `Union` effs2)
              ((oeffs1 :\\ effs2) `Union` oeffs2)
              (ts1 :++ ts2)
              cs2
fuseAT' at1 at2 = weakenCS (fuseAT at1 at2)

-- | `fuseAppAT` is a variant of `fuseAT` that has a cruder type but better runtime
-- performance. When @effs1@ and @effs2@ are disjoint and @oeffs1@ and @oeffs2@
-- are disjoint, the behaviours of @fuseAppAT@ and @fuseAT@ are exactly the
-- same. `fuseAppAT` is faster than `fuseAT` because `fuseAppAT` avoids
-- `weakenAlg`, which constructs its entries by repetitively @cons@-ing.

{-# INLINE fuseAppAT #-}
fuseAppAT
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( CompAT# ts1 ts2, ForwardsC cs1 effs2 ts1, ForwardsC cs2 oeffs1 ts2, KnownEffs oeffs1 )
  => AlgTrans effs1 oeffs1 ts1 cs1
     -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs2 ts2 cs2
     -- ^ The second algebra transformer
  -> AlgTrans (effs1 :++ effs2)
              (oeffs1 :++ oeffs2)
              (ts1 :++ ts2)
              (CompC ts2 cs1 cs2)
fuseAppAT at1 at2 = AlgTrans $ \(oalg :: Algebra (oeffs1 :++ oeffs2) m) ->
  let (oalg1, oalg2) = splitAlg @oeffs1 @oeffs2 oalg
  in appendAlg @effs1 @effs2 @(Apply (ts1 :++ ts2) m)
       (getAT at1 (getAT (fwds @oeffs1 @ts2) oalg1))
       (getAT (fwds @effs2 @ts1) (getAT at2 oalg2))

infixr 9 `pipeAT`

type PipeAT# effs2 oeffs1 oeffs2 ts1 ts2 =
   ( Members (oeffs1 :\\ effs2) ((oeffs1 :\\ effs2) `Union` oeffs2)
   , Members oeffs2 ((oeffs1 :\\ effs2) `Union` oeffs2)
   , Members oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
   , forall m . Assoc ts1 ts2 m )

-- | @pipeAT at1 at2@ composes @at1@ and @at2@ in a way that
--    1. the input effects @effs2@ of @at2@ are /not/ visible in the input effects of the final result, and
--    2. the output effects @oeffs1@ of @at1@ are intercepted by @effs2@ as much as possible.
{-# INLINE pipeAT #-}
pipeAT
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( ForwardsC cs2 (oeffs1 :\\ effs2) ts2
     , PipeAT# effs2 oeffs1 oeffs2 ts1 ts2 )
  => AlgTrans effs1 oeffs1 ts1 cs1
     -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs2 ts2 cs2
     -- ^ The second algebra transformer
  -> AlgTrans effs1
              ((oeffs1 :\\ effs2) `Union` oeffs2)
              (ts1 :++ ts2)
              (CompC ts2 cs1 cs2)
-- We can define pipeAT as:
--
-- > pipeAT at1 at2 = generalFuse (Proxy @'[]) (Proxy @effs2) at1 at2
--
-- But this would result in some always-true but complex constraints, so let's
-- give a direct definition:
pipeAT at1 at2 = AlgTrans $ \oalg ->
  getAT at1 (weakenAlg $
    appendAlg @(oeffs1 :\\ effs2) @effs2
      (getAT (fwds @(oeffs1 :\\ effs2) @ts2) (weakenAlg oalg))
      (getAT at2 (weakenAlg oalg)))

infixr 9 `passAT`

type PassAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 =
   ( Members (effs2 :\\ effs1) effs2
   , Members oeffs2 (oeffs1 `Union` oeffs2)
   , Members oeffs1 (oeffs1 `Union` oeffs2)
   , forall m. Assoc ts1 ts2 m )

-- | @passAT at1 at2@ composes @at1@ and @at2@ in a no-interference way that
--    1. all the input effects @effs2@ of @at2@ are visible in the input effects of the final result, and
--    2. the output effects @oeffs1@ of @at1@ are /not/ intercepted by @effs2@ at all.
-- If an effect is in the intersection of @effs1@ and @effs2@, it is handled by @at1@.
{-# INLINE passAT #-}
passAT
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( ForwardsC cs1 effs2 ts1
     , ForwardsC cs2 oeffs1 ts2
     , PassAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 )
  => AlgTrans effs1 oeffs1 ts1 cs1
     -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs2 ts2 cs2
     -- ^ The second algebra transformer
  -> AlgTrans (effs1 `Union` effs2)
              (oeffs1 `Union` oeffs2)
              (ts1 :++ ts2)
              (CompC ts2 cs1 cs2)
passAT at1 at2 = AlgTrans $ \(oalg :: Algebra (oeffs1 `Union` oeffs2) m) ->
  unionAlg @effs1 @effs2
    (getAT at1 @(Apply ts2 m) (getAT (fwds @oeffs1 @ts2) @m (weakenAlg oalg)))
    (getAT (fwds @effs2 @ts1) (getAT at2 (weakenAlg oalg)))

type PassAT'# effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 =
   (  Members (effs1 :\\ effs2) effs1
    , Members oeffs2 (oeffs1 `Union` oeffs2)
    , Members oeffs1 (oeffs1 `Union` oeffs2)
    , Members (effs1 `Union` effs2) (effs2 `Union` effs1)
    , forall m . Assoc ts1 ts2 m )

infixr 9 `passAT'`

-- | @passAT' at1 at2@ is the same as `passAT` except that if an effect is in the
-- intersection of @effs1@ and @effs2@, it is handled by @at2@.
{-# INLINE passAT' #-}
passAT'
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( ForwardsC cs1 effs2 ts1
     , ForwardsC cs2 oeffs1 ts2
     , PassAT'# effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 )
  => AlgTrans effs1 oeffs1 ts1 cs1
     -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs2 ts2 cs2
     -- ^ The second algebra transformer
  -> AlgTrans (effs1 `Union` effs2)
              (oeffs1 `Union` oeffs2)
              (ts1 :++ ts2)
              (CompC ts2 cs1 cs2)
passAT' at1 at2 = AlgTrans $ \oalg ->
   weakenAlg $ unionAlg @effs2 @effs1
     (getAT (fwds @effs2 @ts1) (getAT at2 (weakenAlg oalg)))
     (getAT at1 (getAT (fwds @oeffs1 @ts2) (weakenAlg oalg)))

type GeneralFuseAT# feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 =
   ( Members (feffs :\\ effs1) feffs
   , forall m . Assoc ts1 ts2 m
   , Members oeffs1 ((oeffs1 :\\ ieffs) :++ ieffs)
   , Members oeffs2             ((oeffs1 :\\ ieffs) :++ (oeffs2 :\\ (oeffs1 :\\ ieffs)))
   , Members (oeffs1 :\\ ieffs) ((oeffs1 :\\ ieffs) :++ (oeffs2 :\\ (oeffs1 :\\ ieffs)))
   )

{-# INLINE generalFuseAT #-}
-- | `generalFuseAT` subsumes @fuseAT@, @passAT@, and @pipeAT@ by having two type arguments
-- @feffs@ and @ieffs@ such that
--   1. @feffs@ is a subset of @effs2@ and it specifies the effects that we want to be
--      forwarded along @ts1@ and exposed by the resulting handler;
--   2. @ieffs@ is a subset of @effs2@ and it specifies the effects that we want to
--      use to intercept the effects produced by @h1@.
-- Therefore @generalFuseAT@ instantiates to
--   1. `fuseAT` with @feffs ~ effs2@ and @ieffs ~ effs2@,
--   2. `pipeAT` with @feffs ~ []@    and @ieffs ~ effs2@,
--   3. `passAT` with @feffs ~ effs2@ and @ieffs ~ []@.
-- (When both @feffs@ and @ieffs@ are empty, @generalFuse@ becomes useless so there
-- isn't this case defined specially.)
generalFuseAT
  :: forall feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( Members feffs effs2
     , Members ieffs effs2
     , ForwardsC cs1 feffs ts1
     , ForwardsC cs2 (oeffs1 :\\ ieffs) ts2
     , GeneralFuseAT# feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 )
  => Proxy feffs
     -- ^ Effects to be forwarded
  -> Proxy ieffs
     -- ^ Effects to be intercepted
  -> AlgTrans effs1 oeffs1 ts1 cs1
     -- ^ The first algebra transformer
  -> AlgTrans effs2 oeffs2 ts2 cs2
     -- ^ The second algebra transformer
  -> AlgTrans (effs1 `Union` feffs)
              ((oeffs1 :\\ ieffs) `Union` oeffs2)
              (ts1 :++ ts2)
              (CompC ts2 cs1 cs2)
generalFuseAT _ _ at1 at2 = AlgTrans $ \oalg ->
   unionAlg @effs1 @feffs
     (getAT at1 (weakenAlg $
       appendAlg @(oeffs1 :\\ ieffs) @ieffs
         (getAT (fwds @(oeffs1 :\\ ieffs) @ts2) (weakenAlg oalg))
         (weakenAlg (getAT at2 (weakenAlg oalg)))))
     (getAT (fwds @feffs @ts1) (weakenAlg (getAT at2 (weakenAlg oalg))))

-- ** Staged algebra transformers
--
-- Combinators for staged algebra transformers mirror those for ordinary algebra
-- transformers. In the future I hope to find a way to unify the dynamic
-- and staged versions into a single definition.

-- | Staged version of 'algTrans1'
algTrans1C
  :: forall eff oeffs ts cs.
     (forall m. cs m => AlgebraC oeffs m -> CodeQ (eff (Apply ts m) -.> Apply ts m))
     -- ^ Transformation for the single effect
  -> AlgTransC '[eff] oeffs ts cs
algTrans1C at = AlgTransC \(oalg :: AlgebraC oeffs m) -> at oalg :#$ emptyAlgC

-- | Staged version of `hideAT`.
hideATC
  :: forall effs' effs oeffs ts cs.
     HideAT# effs effs'
  => AlgTransC effs oeffs ts cs     -- ^ Staged algebra transformer to hide effects from
  -> AlgTransC (effs :\\ effs') oeffs ts cs
hideATC at = AlgTransC \oalg -> weakenAlgC (getATC at oalg)

-- | Staged version of `weakenCS`
weakenCSC
  :: forall cs' cs effs oeffs ts.
     (forall m. cs' m => cs m)
  => AlgTransC effs oeffs ts cs     -- ^ Staged algebra transformer to weaken
  -> AlgTransC effs oeffs ts cs'
weakenCSC at = AlgTransC $ getATC at

-- | Staged version of `weakenCSMonad`
weakenCSCMonad
  :: forall ts2 effs oeffs ts.
     (forall m. Monad m => MonadApply ts2 m)
  => AlgTransC effs oeffs ts (CompC ts2 Monad Monad)
     -- ^ Algebra transformer to weaken
  -> AlgTransC effs oeffs ts Monad
weakenCSCMonad = weakenCSC

-- | Staged version of `withFwdsAT`.
{-# INLINE withFwdsATC #-}
withFwdsATC
  :: forall feffs effs oeffs ts cs.
     ( ForwardsC cs feffs ts
     , WithFwds# effs oeffs feffs )
  => Proxy feffs                                       -- ^ Effects to be forwarded
  -> AlgTransC effs oeffs ts cs                        -- ^ Staged algebra transformer
  -> AlgTransC (effs `Union` feffs) (oeffs `Union` feffs) ts cs
withFwdsATC _ at = AlgTransC $ \oalg ->
  unionAlgC @effs @feffs
    (getATC at (weakenAlgC @oeffs oalg))
    (getATC (fwdsC @feffs @ts) (weakenAlgC @feffs oalg))

-- | Staged version of `withFwdsAT'`.
{-# INLINE withFwdsATC' #-}
withFwdsATC'
  :: forall feffs effs oeffs ts cs.
     ( ForwardsC cs feffs ts
     , WithFwds'# effs oeffs feffs )
  => Proxy feffs                                   -- ^ Effects to be forwarded
  -> AlgTransC effs oeffs ts cs                    -- ^ Staged algebra transformer
  -> AlgTransC (effs :++ feffs) (oeffs :++ feffs) ts cs
withFwdsATC' _ at = AlgTransC $ \oalg ->
  appendAlgC @effs @feffs
    (getATC at (weakenAlgC @oeffs oalg))
    (getATC (fwdsC @feffs @ts) (weakenAlgC @feffs oalg))

-- | Staged version of `fuseAT`
fuseATC
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2
  => ( ForwardsC cs1 effs2 ts1, ForwardsC cs2 (oeffs1 :\\ effs2) ts2 )
  => AlgTransC effs1 oeffs1 ts1 cs1
     -- ^ The first staged algebra transformer
  -> AlgTransC effs2 oeffs2 ts2 cs2
     -- ^ The second staged algebra transformer
  -> AlgTransC (effs1 `Union` effs2)
               ((oeffs1 :\\ effs2) `Union` oeffs2)
               (ts1 :++ ts2)
               (CompC ts2 cs1 cs2)
fuseATC at1 at2 = generalFuseATC (Proxy @effs2) (Proxy @effs2) at1 at2

{-# INLINE fuseAppATC #-}
fuseAppATC
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( CompAT# ts1 ts2, ForwardsC cs1 effs2 ts1, ForwardsC cs2 oeffs1 ts2
     , KnownEffs oeffs1 )
  => AlgTransC effs1 oeffs1 ts1 cs1
     -- ^ The first staged algebra transformer
  -> AlgTransC effs2 oeffs2 ts2 cs2
     -- ^ The second staged algebra transformer
  -> AlgTransC (effs1 :++ effs2)
               (oeffs1 :++ oeffs2)
               (ts1 :++ ts2)
               (CompC ts2 cs1 cs2)
fuseAppATC at1 at2 = AlgTransC $ \(oalg :: AlgebraC (oeffs1 :++ oeffs2) m) ->
  let (oalg1, oalg2) = splitAlgC @oeffs1 @oeffs2 oalg
  in appendAlgC @effs1 @effs2 @(Apply (ts1 :++ ts2) m)
       (getATC at1 (getATC (fwdsC @oeffs1 @ts2) oalg1))
       (getATC (fwdsC @effs2 @ts1) (getATC at2 oalg2))

-- | Staged version of `pipeAT`
pipeATC
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( ForwardsC cs2 (oeffs1 :\\ effs2) ts2
     , PipeAT# effs2 oeffs1 oeffs2 ts1 ts2 )
  => AlgTransC effs1 oeffs1 ts1 cs1
     -- ^ The first staged algebra transformer
  -> AlgTransC effs2 oeffs2 ts2 cs2
     -- ^ The second staged algebra transformer
  -> AlgTransC effs1
               ((oeffs1 :\\ effs2) `Union` oeffs2)
               (ts1 :++ ts2)
               (CompC ts2 cs1 cs2)
pipeATC at1 at2 = AlgTransC $ \oalg ->
  getATC at1 (weakenAlgC $
    appendAlgC @(oeffs1 :\\ effs2) @effs2
      (getATC (fwdsC @(oeffs1 :\\ effs2) @ts2) (weakenAlgC oalg))
      (getATC at2 (weakenAlgC oalg)))

-- | Staged version of `passAT`.
passATC
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( ForwardsC cs1 effs2 ts1
     , ForwardsC cs2 oeffs1 ts2
     , PassAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 )
  => AlgTransC effs1 oeffs1 ts1 cs1
     -- ^ The first staged algebra transformer
  -> AlgTransC effs2 oeffs2 ts2 cs2
     -- ^ The second staged algebra transformer
  -> AlgTransC (effs1 `Union` effs2)
               (oeffs1 `Union` oeffs2)
               (ts1 :++ ts2)
               (CompC ts2 cs1 cs2)
passATC at1 at2 = AlgTransC $ \(oalg :: AlgebraC (oeffs1 `Union` oeffs2) m) ->
  unionAlgC @effs1 @effs2
    (getATC at1 @(Apply ts2 m) (getATC (fwdsC @oeffs1 @ts2) @m (weakenAlgC oalg)))
    (getATC (fwdsC @effs2 @ts1) (getATC at2 (weakenAlgC oalg)))

-- | Staged version of `passAT'`.
passATC'
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( ForwardsC cs1 effs2 ts1
     , ForwardsC cs2 oeffs1 ts2
     , PassAT'# effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 )
  => AlgTransC effs1 oeffs1 ts1 cs1
     -- ^ The first staged algebra transformer
  -> AlgTransC effs2 oeffs2 ts2 cs2
     -- ^ The second staged algebra transformer
  -> AlgTransC (effs1 `Union` effs2)
               (oeffs1 `Union` oeffs2)
               (ts1 :++ ts2)
               (CompC ts2 cs1 cs2)
passATC' at1 at2 = AlgTransC $ \oalg ->
   weakenAlgC $ unionAlgC @effs2 @effs1
     (getATC (fwdsC @effs2 @ts1) (getATC at2 (weakenAlgC oalg)))
     (getATC at1 (getATC (fwdsC @oeffs1 @ts2) (weakenAlgC oalg)))

-- | Staged version of `generalFuseAT`.
generalFuseATC
  :: forall feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
     ( Members feffs effs2
     , Members ieffs effs2
     , ForwardsC cs1 feffs ts1
     , ForwardsC cs2 (oeffs1 :\\ ieffs) ts2
     , GeneralFuseAT# feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 )
  => Proxy feffs
     -- ^ Effects to be forwarded
  -> Proxy ieffs
     -- ^ Intercepted effects
  -> AlgTransC effs1 oeffs1 ts1 cs1
     -- ^ The first staged algebra transformer
  -> AlgTransC effs2 oeffs2 ts2 cs2
     -- ^ The second staged algebra transformer
  -> AlgTransC (effs1 `Union` feffs)
               ((oeffs1 :\\ ieffs) `Union` oeffs2)
               (ts1 :++ ts2)
               (CompC ts2 cs1 cs2)
generalFuseATC _ _ at1 at2 = AlgTransC $ \oalg ->
  unionAlgC @effs1 @feffs
    (getATC at1 (weakenAlgC $
      appendAlgC @(oeffs1 :\\ ieffs) @ieffs
        (getATC (fwdsC @(oeffs1 :\\ ieffs) @ts2) (weakenAlgC oalg))
        (weakenAlgC (getATC at2 (weakenAlgC oalg)))))
    (getATC (fwdsC @feffs @ts1) (weakenAlgC (getATC at2 (weakenAlgC oalg))))