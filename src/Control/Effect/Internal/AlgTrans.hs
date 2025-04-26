{-|
Module      : Control.Effect.Internal.AlgTrans
Description : 
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental
-}
{-# LANGUAGE ImpredicativeTypes, QuantifiedConstraints, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, MonoLocalBinds, LambdaCase, BlockArguments #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Control.Effect.Internal.AlgTrans 
  ( module Control.Effect.Internal.AlgTrans.Type
  , module Control.Effect.Internal.AlgTrans 
  ) where

import Data.List.Kind ( Union, (:\\), (:++) )
import Data.HFunctor ( HFunctor )

import Control.Effect.Internal.Effs
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Prog.ProgImp ( Prog, eval )
import Control.Effect.Internal.Forward.ForwardC

-- * Using algebra transformers and runners 

{-# INLINE evalTr #-}
evalTr :: forall effs oeffs xeffs ts cs m a. 
       ( HFunctor (Effs effs) 
       , cs m
       , Injects oeffs xeffs
       , Monad (Apply ts m) )
       => Algebra xeffs m
       -> AlgTrans effs oeffs ts cs
       -> Prog effs a
       -> Apply ts m a
evalTr oalg alg = eval (getAT alg (oalg . injs)) 

{-# INLINE evalTr' #-}
evalTr' :: forall effs ts cs m a. 
        ( HFunctor (Effs effs) 
        , cs m
        , Monad (Apply ts m) )
        => AlgTrans effs '[] ts cs
        -> Prog effs a
        -> Apply ts m a
evalTr' alg = eval (getAT alg (absurdEffs @m)) 

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

-- | A constraint synonym that is frequently used when composing algebra transformers. 
class    (cs2 m, cs1 (Apply ts2 m)) => CompC ts2 cs1 cs2 m where
instance (cs2 m, cs1 (Apply ts2 m)) => CompC ts2 cs1 cs2 m where

-- | Boring constraints that will always be satisfied automatically when the parameters
-- are substituted by concrete values. Users don't need to care about them.
type AutoCompAT ts1 ts2 effs1 cs2 = ( forall m . Assoc ts1 ts2 m )

-- | Composing two algebra transformers.
{-# INLINE compAT #-}
compAT :: forall effs1 effs2 effs3 ts1 ts2 cs1 cs2.
          ( AutoCompAT ts1 ts2 effs1 cs2 )
       => AlgTrans effs1 effs2 ts1 cs1
       -> AlgTrans effs2 effs3 ts2 cs2
       -> AlgTrans effs1 effs3 (ts1 :++ ts2) (CompC ts2 cs1 cs2)
compAT alg1 alg2 = AlgTrans \(oalg :: Algebra effs3 m) -> getAT alg1 (getAT alg2 oalg) 

-- | Every algebra transformer can be used as one that processes fewer input effects,
-- generating more output effects, and/or with stronger input constraints.
{-# INLINE weakenAT #-}
weakenAT :: (Injects effs' effs, Injects oeffs oeffs', forall m. cs' m => cs m)
         => AlgTrans effs  oeffs  ts cs
         -> AlgTrans effs' oeffs' ts cs'
weakenAT at = AlgTrans \oalg x -> getAT at (oalg . injs) (injs x)

-- | A synonym for the conjunction of two constraints @cs1@ and @cs2@ on @m@.
class (cs1 m, cs2 m) => AndC cs1 cs2 m where
instance (cs1 m, cs2 m) => AndC cs1 cs2 m where

type AutoCaseTrans effs1 effs2 = (Append effs1 (effs2 :\\ effs1), Injects (effs2 :\\ effs1) effs2)

{-# INLINE caseAT #-}
caseAT :: forall effs1 effs2 cs1 cs2 oeffs ts. 
          AutoCaseTrans effs1 effs2
       => AlgTrans effs1 oeffs ts cs1
       -> AlgTrans effs2 oeffs ts cs2
       -> AlgTrans (effs1 `Union` effs2) oeffs ts (AndC cs1 cs2)
caseAT at1 at2 = AlgTrans \oalg -> hunion (getAT at1 oalg) (getAT at2 oalg)

type AutoCaseTrans' effs1 effs2 = (Append effs1 effs2)

{-# INLINE caseAT' #-}
caseAT' :: forall effs1 effs2 cs1 cs2 oeffs ts. 
          (AutoCaseTrans' effs1 effs2)
        => AlgTrans effs1 oeffs ts cs1
        -> AlgTrans effs2 oeffs ts cs2
        -> AlgTrans (effs1 :++ effs2) oeffs ts (AndC cs1 cs2)
caseAT' at1 at2 = AlgTrans \oalg -> heither (getAT at1 oalg) (getAT at2 oalg)


-- ** Derived combinators of algebra transformers

{-# INLINE weakenC #-}
weakenC :: forall cs' cs effs oeffs ts. 
          (forall m. cs' m => cs m)
       => AlgTrans effs oeffs ts cs
       -> AlgTrans effs oeffs ts cs'
weakenC at = AlgTrans \oalg x -> getAT at oalg x

{-# INLINE weakenEffs #-}
weakenEffs 
       :: (Injects effs' effs, Injects oeffs oeffs')
       => AlgTrans effs  oeffs  ts cs
       -> AlgTrans effs' oeffs' ts cs
weakenEffs = weakenAT

{-# INLINE weakenOEffs #-}
weakenOEffs :: forall oeffs' oeffs effs ts cs. 
          Injects oeffs oeffs'
       => AlgTrans effs oeffs  ts cs
       -> AlgTrans effs oeffs' ts cs
weakenOEffs at = AlgTrans \ oalg x -> getAT at (oalg . injs) x

{-# INLINE weakenIEffs #-}
weakenIEffs :: forall effs' effs oeffs ts cs.
          Injects effs' effs
       => AlgTrans effs  oeffs ts cs
       -> AlgTrans effs' oeffs ts cs
weakenIEffs at = AlgTrans \ oalg x -> getAT at oalg (injs x)

{-# INLINE caseATSameC #-}
caseATSameC 
       :: forall effs1 effs2 cs oeffs ts. 
          AutoCaseTrans effs1 effs2
       => AlgTrans effs1 oeffs ts cs
       -> AlgTrans effs2 oeffs ts cs
       -> AlgTrans (effs1 `Union` effs2) oeffs ts cs
caseATSameC at1 at2 = AlgTrans \oalg -> hunion (getAT at1 oalg) (getAT at2 oalg)

{-# INLINE caseATSameC' #-}
caseATSameC'
       :: forall effs1 effs2 cs oeffs ts. 
           AutoCaseTrans' effs1 effs2
        => AlgTrans effs1 oeffs ts cs
        -> AlgTrans effs2 oeffs ts cs
        -> AlgTrans (effs1 :++ effs2) oeffs ts cs
caseATSameC' at1 at2 = AlgTrans \oalg -> heither (getAT at1 oalg) (getAT at2 oalg)


{-# INLINE withFwds #-}
withFwds :: forall xeffs effs oeffs ts cs1 cs2. 
            ( ForwardsC cs2 xeffs ts, Injects xeffs oeffs
            , AutoCaseTrans effs xeffs )
         => AlgTrans effs oeffs ts cs1
         -> AlgTrans (effs `Union` xeffs) oeffs ts (AndC cs1 cs2)
withFwds at = caseAT at (weakenOEffs @oeffs @xeffs fwdsC)


{-# INLINE withFwds' #-}
withFwds' :: forall xeffs effs oeffs ts cs1 cs2. 
            ( ForwardsC cs2 xeffs ts, Injects xeffs oeffs
            , AutoCaseTrans' effs xeffs )
         => AlgTrans effs oeffs ts cs1
         -> AlgTrans (effs :++ xeffs) oeffs ts (AndC cs1 cs2)
withFwds' at = caseAT' at (weakenOEffs @oeffs @xeffs fwdsC)


{-# INLINE withFwdsSameC #-}
withFwdsSameC
         :: forall xeffs effs oeffs ts cs. 
            ( ForwardsC cs xeffs ts, Injects xeffs oeffs
            , AutoCaseTrans effs xeffs )
         => AlgTrans effs oeffs ts cs
         -> AlgTrans (effs `Union` xeffs) oeffs ts cs
withFwdsSameC at = caseATSameC at (weakenOEffs @oeffs @xeffs fwdsC)


{-# INLINE withFwdsSameC' #-}
withFwdsSameC' :: forall xeffs effs oeffs ts cs. 
            ( ForwardsC cs xeffs ts, Injects xeffs oeffs
            , AutoCaseTrans' effs xeffs )
         => AlgTrans effs oeffs ts cs
         -> AlgTrans (effs :++ xeffs) oeffs ts cs
withFwdsSameC' at = caseATSameC' at (weakenOEffs @oeffs @xeffs fwdsC)


type AutoFuseAT effs1 effs2 oeffs1 oeffs2 ts1 ts2 = 
   ( Injects (oeffs1 :\\ effs2) ((oeffs1 :\\ effs2) `Union` oeffs2)
   , Injects (effs2 :\\ effs1) effs2
   , Injects oeffs2 ((oeffs1 :\\ effs2) `Union` oeffs2)
   , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
   , Append (oeffs1 :\\ effs2) effs2
   , Append effs1 (effs2 :\\ effs1)
   , forall m . Assoc ts1 ts2 m 
   )

-- | @fuseAT at1 at2@ composes @at1@ and @at2@ in a way that uses @at2@ maximally:
--    1. all the input effects @effs2@ of @at2@ are visible in the input effects of the final result, and
--    2. the output effects @oeffs1@ of @at1@ are intercepted by @effs2@ as much as possible.
{-# INLINE fuseAT #-}
fuseAT :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
          ( ForwardsC cs1 effs2 ts1
          , ForwardsC cs2 (oeffs1 :\\ effs2) ts2
          , AutoFuseAT effs1 effs2 oeffs1 oeffs2 ts1 ts2 )
       => AlgTrans effs1 oeffs1 ts1 cs1 
       -> AlgTrans effs2 oeffs2 ts2 cs2
       -> AlgTrans (effs1 `Union` effs2) 
                   ((oeffs1 :\\ effs2) `Union` oeffs2) 
                   (ts1 :++ ts2)
                   (CompC ts2 cs1 cs2)
fuseAT at1 at2 = AlgTrans $ \(oalg :: Algebra _ m) -> 
    hunion @effs1 @effs2
      (getAT at1 (weakenAlg $
        heither @(oeffs1 :\\ effs2) @effs2
          (getAT (fwdsC @cs2 @(oeffs1 :\\ effs2) @ts2) (weakenAlg oalg))
          (getAT at2 (weakenAlg oalg))))
      (getAT (fwdsC @cs1 @effs2 @ts1) (getAT at2 (oalg . injs)))


type AutoPipeAT effs2 oeffs1 oeffs2 ts1 ts2 = 
   ( Injects (oeffs1 :\\ effs2) ((oeffs1 :\\ effs2) `Union` oeffs2)
   , Injects oeffs2 ((oeffs1 :\\ effs2) `Union` oeffs2)
   , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
   , Append (oeffs1 :\\ effs2) effs2
   , forall m . Assoc ts1 ts2 m )

-- | @pipeAT at1 at2@ composes @at1@ and @at2@ in a way that 
--    1. the input effects @effs2@ of @at2@ are /not/ visible in the input effects of the final result, and
--    2. the output effects @oeffs1@ of @at1@ are intercepted by @effs2@ as much as possible.
{-# INLINE pipeAT #-}
pipeAT :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
          ( ForwardsC cs2 (oeffs1 :\\ effs2) ts2
          , AutoPipeAT effs2 oeffs1 oeffs2 ts1 ts2 )
       => AlgTrans effs1 oeffs1 ts1 cs1 
       -> AlgTrans effs2 oeffs2 ts2 cs2
       -> AlgTrans effs1 
                   ((oeffs1 :\\ effs2) `Union` oeffs2) 
                   (ts1 :++ ts2)
                   (CompC ts2 cs1 cs2)
pipeAT at1 at2 = AlgTrans $ \(oalg :: Algebra _ m) -> 
  getAT at1 (weakenAlg $
    heither @(oeffs1 :\\ effs2) @effs2
      (getAT (fwdsC @cs2 @(oeffs1 :\\ effs2) @ts2) (weakenAlg oalg))
      (getAT at2 (weakenAlg oalg)))


type AutoPassAT effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 = 
   ( Injects (effs2 :\\ effs1) effs2
   , Injects oeffs2 (oeffs1 `Union` oeffs2)
   , Injects oeffs1 (oeffs1 `Union` oeffs2)
   , Append effs1 (effs2 :\\ effs1)
   , forall m. Assoc ts1 ts2 m )

-- | @passAT at1 at2@ composes @at1@ and @at2@ in a way that 
--    1. all the input effects @effs2@ of @at2@ are visible in the input effects of the final result, and
--    2. the output effects @oeffs1@ of @at1@ are /not/ intercepted by @effs2@ at all.
-- If an effect is in the intersection of @effs1@ and @effs2@, it is handled by @at1@.
{-# INLINE passAT #-}
passAT :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
          ( ForwardsC cs1 effs2 ts1
          , ForwardsC cs2 oeffs1 ts2
          , AutoPassAT effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 )
       => AlgTrans effs1 oeffs1 ts1 cs1 
       -> AlgTrans effs2 oeffs2 ts2 cs2
       -> AlgTrans (effs1 `Union` effs2) 
                   (oeffs1 `Union` oeffs2) 
                   (ts1 :++ ts2)
                   (CompC ts2 cs1 cs2)
passAT at1 at2 = AlgTrans $ \(oalg :: Algebra _ m) -> 
  hunion @effs1 @effs2
    (getAT at1 @(Apply ts2 m) (getAT (fwdsC @cs2 @oeffs1 @ts2) @m (oalg . injs)))
    (getAT (fwdsC @cs1 @effs2 @ts1) (getAT at2 (oalg . injs)))


type AutoPassAT' effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 = 
   (  Injects (effs1 :\\ effs2) effs1
    , Injects oeffs2 (oeffs1 `Union` oeffs2)
    , Injects oeffs1 (oeffs1 `Union` oeffs2)
    , Injects (effs1 `Union` effs2) (effs2 `Union` effs1)
    , Append effs2 (effs1 :\\ effs2)
    , forall m . Assoc ts1 ts2 m )

-- | @passAT' at1 at2@ is the same as `passAT` except that if an effect is in the 
-- intersection of @effs1@ and @effs2@, it is handled by @at2@.
{-# INLINE passAT' #-}
passAT' :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
        ( ForwardsC cs1 effs2 ts1
        , ForwardsC cs2 oeffs1 ts2
        , AutoPassAT' effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs2 )
        => AlgTrans effs1 oeffs1 ts1 cs1 
        -> AlgTrans effs2 oeffs2 ts2 cs2
        -> AlgTrans (effs1 `Union` effs2) 
                     (oeffs1 `Union` oeffs2) 
                     (ts1 :++ ts2)
                     (CompC ts2 cs1 cs2)
passAT' at1 at2 = AlgTrans $ \(oalg :: Algebra _ m) -> 
  hunion @effs2 @effs1
      (getAT (fwdsC @cs1 @effs2 @ts1) (getAT at2 (oalg . injs)))
      (getAT at1 (getAT (fwdsC @cs2 @oeffs1 @ts2) (oalg . injs)))
  . injs