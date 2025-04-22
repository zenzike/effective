{-# LANGUAGE ImpredicativeTypes, QuantifiedConstraints, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, MonoLocalBinds, LambdaCase, BlockArguments #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Control.Effect.Internal.Handler.LowLevel where

import Control.Effect.Internal.Handler.Type
import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Handler.Forward

import Unsafe.Coerce
import Data.List.Kind
import Data.Functor.Identity
import Data.Functor.Compose
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Compose
import Data.HFunctor

-- * Using algebra transformers and runners 
--
-- The type families @`HApply` ts@ and @`Apply` fs@ remove newtype wrappers so
-- it is safe to coerce them into @ts@ and @fs@ respectively. (I don't know how
-- to convince GHC that this is a safe coerce.) 

under :: a -> (a -> b) -> b
under x f = f x

under' :: (a -> b) -> (b -> c) -> a -> c
under' f g = g . f

{-# INLINE evalTr #-}
evalTr :: forall effs ts cs m a. 
       ( HFunctor (Effs effs) 
       , cs m
       , Monad (ts m) )
       => AlgTrans effs '[] ts cs
       -> Prog effs a
       -> HApply ts m a
evalTr alg = eval (getAT alg absurdEffs) 
  `under'` unsafeCoerce @(ts m a) @(HApply ts m a) 

{-# INLINE run #-}
run :: forall oeffs ts fs cs m x.
       cs m 
    => Runner oeffs ts fs cs 
    -> Algebra oeffs m 
    -> ts m x -> m (Apply fs x)
run r oalg t = getR r oalg t 
  `under` unsafeCoerce @(m (fs x)) @(m (Apply fs x)) 

-- * Building algebra transformers

-- ** Primitive combinators

class (m ~ n) => Is m n where
instance (m ~ n) => Is m n where

-- | Treating an algebra on @m@ as a trivial algebra transformer that only works
-- when the carrier is exactly @m@.
{-# INLINE asAT #-}
asAT :: forall effs m. Algebra effs m -> AlgTrans effs '[] IdentityT (Is m)
asAT alg = AlgTrans \_ -> alg
  `under` unsafeCoerce @(Algebra effs m) @(Algebra effs (IdentityT m)) 

-- | The identity algebra transformer.
{-# INLINE idAT #-}
idAT :: forall effs cs. AlgTrans effs effs IdentityT cs
idAT = AlgTrans \(alg :: Algebra effs m) -> alg
  `under` unsafeCoerce @(Algebra effs m) @(Algebra effs (IdentityT m)) 

class (cs2 m, cs1 (ts2 m)) => CompATC ts2 cs1 cs2 m where
instance (cs2 m, cs1 (ts2 m)) => CompATC ts2 cs1 cs2 m where

{-# INLINE compAT #-}
compAT :: forall effs1 effs2 effs3 ts1 ts2 cs1 cs2.
         AlgTrans effs1 effs2 ts1 cs1
       -> AlgTrans effs2 effs3 ts2 cs2
       -> AlgTrans effs1 effs3 (ts1 `ComposeT` ts2) (CompATC ts2 cs1 cs2)
compAT alg1 alg2 = AlgTrans \oalg -> getAT alg1 (getAT alg2 oalg)
  `under` unsafeCoerce @(Algebra effs1 (ts1 (ts2 _))) 
                       @(Algebra effs1 (ComposeT ts1 ts2 _))

{-# INLINE weaken #-}
weaken :: (Injects effs' effs, Injects oeffs oeffs', forall m. cs' m => cs m)
       => AlgTrans effs  oeffs  ts cs
       -> AlgTrans effs' oeffs' ts cs'
weaken at = AlgTrans \oalg x -> getAT at (oalg . injs) (injs x)

class (cs1 m, cs2 m) => AndC cs1 cs2 m where
instance (cs1 m, cs2 m) => AndC cs1 cs2 m where

type AutoCaseTrans effs1 effs2 = (Append effs1 (effs2 :\\ effs1), Injects (effs2 :\\ effs1) effs2)
{-# INLINE caseAT #-}
caseAT :: forall effs1 effs2 cs1 cs2 oeffs ts. 
          (AutoCaseTrans effs1 effs2)
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
weakenEffs = weaken

{-# INLINE weakenOEffs #-}
weakenOEffs :: forall oeffs' oeffs effs ts cs. 
          (Injects oeffs oeffs')
       => AlgTrans effs oeffs  ts cs
       -> AlgTrans effs oeffs' ts cs
weakenOEffs at = AlgTrans \ oalg x -> getAT at (oalg . injs) x

{-# INLINE weakenIEffs #-}
weakenIEffs :: forall effs' effs oeffs ts cs.
          (Injects effs' effs)
       => AlgTrans effs  oeffs ts cs
       -> AlgTrans effs' oeffs ts cs
weakenIEffs at = AlgTrans \ oalg x -> getAT at oalg (injs x)

{-# INLINE withFwds #-}
withFwds :: forall xeffs effs oeffs ts cs1 cs2. 
            ( Forwards cs2 xeffs ts, Injects xeffs oeffs
            , AutoCaseTrans effs xeffs )
         => AlgTrans effs oeffs ts cs1
         -> AlgTrans (effs `Union` xeffs) oeffs ts (AndC cs1 cs2)
withFwds at = caseAT at (weakenOEffs @oeffs @xeffs fwds)

{-# INLINE withFwds' #-}
withFwds' :: forall xeffs effs oeffs ts cs1 cs2. 
            ( Forwards cs2 xeffs ts, Injects xeffs oeffs
            , AutoCaseTrans' effs xeffs )
         => AlgTrans effs oeffs ts cs1
         -> AlgTrans (effs :++ xeffs) oeffs ts (AndC cs1 cs2)
withFwds' at = caseAT' at (weakenOEffs @oeffs @xeffs fwds)

type AutoFuseAT effs1 effs2 oeffs1 oeffs2 = 
   (  Injects (oeffs1 :\\ effs2) ((oeffs1 :\\ effs2) `Union` oeffs2)
    , Injects (effs2 :\\ effs1) effs2
    , Injects oeffs2 ((oeffs1 :\\ effs2) `Union` oeffs2)
    , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
    , Append (oeffs1 :\\ effs2) effs2
    , Append effs1 (effs2 :\\ effs1)
   )

-- | `fuseAT at1 at2` composes @at1@ and @at2@ in a way that uses @at2@ maximally:
--    1. all the input effects @effs2@ of @at2@ are visible in the input effects of the final result, and
--    2. the output effects @oeffs1@ of @at1@ are intercepted by @effs2@ as much as possible.
{-# INLINE fuseAT #-}
fuseAT :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 cs1 cs2.
          ( Forwards cs1 effs2 ts1
          , Forwards cs2 (oeffs1 :\\ effs2) ts2
          , AutoFuseAT effs1 effs2 oeffs1 oeffs2
          )
       => AlgTrans effs1 oeffs1 ts1 cs1 
       -> AlgTrans effs2 oeffs2 ts2 cs2
       -> AlgTrans (effs1 `Union` effs2) 
                   ((oeffs1 :\\ effs2) `Union` oeffs2) 
                   (HRAssoc (ComposeT ts1 ts2))
                   (CompATC ts2 cs1 cs2)
fuseAT at1 at2 = AlgTrans $ \(oalg :: Algebra _ m) -> 
      unsafeCoerce @(ts1 (ts2 m) _) @((HRAssoc (ComposeT ts1 ts2)) m _)
    . hunion @effs1 @effs2
        (getAT at1 (weakenAlg $
          heither @(oeffs1 :\\ effs2) @effs2
            (getAT (fwds @cs2 @(oeffs1 :\\ effs2) @ts2) (weakenAlg oalg))
            (getAT at2 (weakenAlg oalg))))
        (getAT (fwds @cs1 @effs2 @ts1) (getAT at2 (oalg . injs)))
    . unsafeCoerce @(Effs _effs (HRAssoc (ComposeT ts1 ts2) m) _) @(Effs _effs (ts1 (ts2 m)) _)

-- * Building runners

{-# INLINE idRunner #-}
idRunner :: (forall m. cs m => Functor m) 
         => Runner effs IdentityT Identity cs
idRunner = Runner \_ (IdentityT x) -> fmap Identity x

{-# INLINE compRunner #-}
compRunner :: forall effs1 effs2 ts1 ts2 fs1 fs2 cs1 cs2.
              (forall m. cs2 m => Functor m)
           => AlgTrans effs1 effs2 ts2 cs2
           -> Runner effs1 ts1 fs1 cs1
           -> Runner effs2 ts2 fs2 cs2
           -> Runner effs2 (ComposeT ts1 ts2) (Compose fs2 fs1) (CompATC ts2 cs1 cs2)
compRunner at r1 r2 = Runner \oalg (ComposeT ts12) ->
   fmap Compose (getR r2 oalg (getR r1 (getAT at oalg) ts12))

type AutoFuseR effs2 oeffs1 oeffs2 = 
   (  Injects (oeffs1 :\\ effs2) ((oeffs1 :\\ effs2) `Union` oeffs2)
    , Injects oeffs2 ((oeffs1 :\\ effs2) `Union` oeffs2)
    , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
    , Append (oeffs1 :\\ effs2) effs2
   )

{-# INLINE fuseR #-}
fuseR :: forall effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2 cs1 cs2.
          ( Forwards cs1 effs2 ts1
          , Forwards cs2 (oeffs1 :\\ effs2) ts2
          , AutoFuseR effs2 oeffs1 oeffs2
          )
       => AlgTrans effs2 oeffs2 ts2 cs2
       -> Runner oeffs1 ts1 fs1 cs1 
       -> Runner oeffs2 ts2 fs2 cs2
       -> Runner ((oeffs1 :\\ effs2) `Union` oeffs2) 
                 (HRAssoc (ComposeT ts1 ts2))
                 (RAssoc (Compose fs2 fs1))
                 (CompATC ts2 cs1 cs2)
fuseR at2 r1 r2 = Runner \(oalg :: Algebra _ m) ->
      unsafeCoerce @(m (fs2 (fs1 _x))) @(m ((RAssoc (Compose fs2 fs1)) _x))
    . getR r2 (oalg . injs)
    . getR r1 (weakenAlg @oeffs1 @((oeffs1 :\\ effs2) :++ effs2) $
        heither @(oeffs1 :\\ effs2) @effs2
          (getAT (fwds @cs2 @(oeffs1 :\\ effs2) @(ts2))
            (weakenAlg @(oeffs1 :\\ effs2) @_ oalg))
          (getAT at2 (weakenAlg @oeffs2 @_ oalg)))
    . unsafeCoerce @(HRAssoc (ComposeT ts1 ts2) m _) @(ts1 (ts2 m) _)