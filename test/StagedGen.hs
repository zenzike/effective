{-# LANGUAGE BlockArguments, TemplateHaskell, ImpredicativeTypes, PartialTypeSignatures, LambdaCase, TypeFamilies, PackageImports #-}
module StagedGen where

import Control.Effect
import Control.Effect.CodeGen
import Control.Effect.CodeGen.Nondet
import Control.Effect.Yield
import Control.Effect.State.Strict
import Control.Effect.Reader
import Control.Effect.Except
import qualified Control.Effect.Maybe as Mb
import Control.Effect.Maybe (MaybeT(..))
import Control.Effect.Nondet.Alternative
import Control.Monad.Trans.Push
import Control.Effect.Yield
import Data.Functor.Identity
import Data.Iso
import Control.Monad (ap)


{-
The following is up and down for the special case @PushT Gen@.
If you are puzzled by the general case, having a look at the special version may
be helpful. I will keep it here for a while for playing.
-}

newtype LG a  = LG {runLG :: forall t. (a -> Gen (CodeQ t) -> Gen (CodeQ t))
                          -> Gen (CodeQ t) -> Gen (CodeQ t)}

instance Functor LG where
  fmap f lg = do x <- lg; return (f x)

instance Applicative LG where
  f <*> x = do f' <- f; x' <- x; return (f' x')
  pure x = LG $ \c n -> c x n
instance Monad LG where
  lg >>= k = LG $ \c n -> runLG lg (\a as -> runLG (k a) c as) n

upLG :: CodeQ [a] -> LG (CodeQ a)
upLG cl = LG $ \c n -> upGen [||
  foldr (\a ms -> $$(downGen (c [||a||] (upGen [||ms||]))))
        $$(downGen n)
        $$cl
  ||]

downLG :: LG (CodeQ a) -> CodeQ [a]
downLG lg = downGen (runLG lg (\a gas -> fmap (\as -> [|| $$a : $$as ||]) gas) (upGen [||[]||]))

upGen :: forall a. CodeQ a -> Gen (CodeQ a)
upGen c = return c

downGen :: forall a. Gen (CodeQ a) -> CodeQ a
downGen g = unGen g id

choiceGen :: forall effs m. Members '[CodeGen, UpOp m, Choose, Empty] effs
          => CodeQ Int -> CodeQ (Int -> m Int) -> Prog effs (CodeQ Int)
choiceGen cN self =
  do b <- split [|| $$cN > 0 ||]
     if b
      then up [|| $$self ($$cN - 1) ||] <|> return cN
      else empty


mergeMb :: MaybeT Gen (CodeQ a) -> MaybeT Gen (CodeQ a)
mergeMb ma = shiftMb \kj kn -> runGen $
  do kN <- genLet_ [|| $$kn ||]
     kJ <- genLet_ [|| \a -> $$(kj ([||a||])) ||]
     m <- runMaybeT ma
     case m of
       Nothing -> return kN
       Just a  -> return ([|| $$kJ $$a ||])

shiftMb :: (forall r. (a -> CodeQ r) -> CodeQ r -> CodeQ r)
        -> MaybeT Gen a
shiftMb f = MaybeT $ shiftGen \k -> return (f (k . Just) (k Nothing))

resetMb :: forall a. MaybeT Gen (CodeQ a) -> MaybeT Gen (CodeQ a)
resetMb g =
  let act :: CodeQ (MaybeT Identity a)
      act = down g
  in MaybeT do genSplit [|| runIdentity (runMaybeT $$act) ||]

{-
shift :: (forall r. (a -> CodeQ r) -> Gen (CodeQ r)) -> Gen a
shift f = Gen $ runGen . f
-}

mergeST :: StateT (CodeQ s) Gen (CodeQ a) -> StateT (CodeQ s) Gen (CodeQ a)
mergeST ma = StateT \s -> shiftGen \k ->
  do k' <- genLet_ [|| \a s -> $$(k ([||a||], [||s||])) ||]
     (a, s) <- runStateT ma s
     return [|| $$k' $$a $$s ||]


mergePS :: PushT Gen (CodeQ a) -> PushT Gen (CodeQ a)
mergePS ma = PushT \kc kn ->
  do kn' <- genLet_ [|| runIdentity $$(down kn) ||]
     kc' <- genLet_ [|| \a t -> runIdentity $$(down (kc [||a||] (return [||runIdentity t||]))) ||]
     runPushT ma (\ca mas -> return [|| $$kc' $$ca $$(down mas) ||]) (return kn')

noJoinProg :: (Members '[Put (CodeQ Int), Get (CodeQ Int), Mb.Throw, Mb.Catch, CodeGen] effs)
         => CodeQ Bool -> Prog effs (CodeQ ())
noJoinProg b =
  do genCase b (\case
         True  -> putC [|| 10 :: Int ||]
         False -> putC [|| 20 :: Int ||])
     s <- getC @Int
     put [|| $$s + $$s ||]
     return [|| () ||]

resetProg :: (Members '[Put (CodeQ Int), Get (CodeQ Int), Mb.Throw, Mb.Catch, CodeGen, Reset] effs)
         => CodeQ Bool -> Prog effs (CodeQ ())
resetProg b =
  do reset $ genCase b (\case
         True  -> putC [|| 10 :: Int ||] >> return [||()||]
         False -> putC [|| 20 :: Int ||] >> return [||()||])
     s <- getC @Int
     put [|| $$s + $$s ||]
     return [|| () ||]

joinProg :: (Members '[Put (CodeQ Int), Get (CodeQ Int), Mb.Throw, CodeGen, JoinFlow] effs)
         => CodeQ Bool -> Prog effs (CodeQ ())
joinProg b =
  do joinFlow $ genCase b (\case
         True  -> putC [|| 10 :: Int ||]
         False -> putC [|| 20 :: Int ||])
     s <- getC @Int
     put [|| $$s + $$s ||]
     return [|| () ||]


ioProg :: Members '[UpOp IO, UpOp m, CodeGen, Put (CodeQ Int), Get (CodeQ Int)] effs
       => CodeQ (m ()) -> Prog effs (CodeQ ())
ioProg self =
  do up [|| putStrLn "Hello" ||]
     s <- get @(CodeQ Int)
     b <- split [|| $$s > 0 ||]
     if b then put [|| $$s - 1||] >> up self
          else return [||()||]

yieldGen :: Members '[Yield (CodeQ Int) (CodeQ Int), CodeGen, UpOp m] effs
         => CodeQ (Int -> m Int) -> CodeQ Int -> Prog effs (CodeQ Int)
yieldGen self i =
  do i' <- split [|| even $$i ||] >>= \case
        True -> genLet [|| $$i `div` 2 ||]
        _    -> genLet [|| 3 * $$i + 1 ||]
     i'' <- yield i'
     up [|| $$self $$i'' ||]


-- The following programs are the tests from the heftia benchmark
--
catchGen :: forall effs m. Members '[CodeGen, UpOp m, Catch (CodeQ ()), Throw (CodeQ ())] effs 
         => CodeQ Int -> CodeQ (Int -> m ()) -> Prog effs (CodeQ ())
catchGen cN self = 
  do b <- split [|| $$cN > 0 ||]
     if b 
      then catch (up [|| $$self ($$cN - 1)||]) (\(_ :: CodeQ ()) -> throw @(CodeQ ()) [||()||])
      else throw @(CodeQ ()) [|| () ||]

countdownGen :: Members '[CodeGen, UpOp m, Put (CodeQ Int), Get (CodeQ Int)] effs 
             => CodeQ (m ()) -> Prog effs (CodeQ ())
countdownGen self = 
  do cs <- get @(CodeQ Int)
     b <- split [|| $$cs > 0 ||]
     if b then do put [|| $$cs - 1 ||]; up self
          else return [|| () ||]

localGen :: forall effs m. Members '[CodeGen, UpOp m, Ask (CodeQ Int), Local (CodeQ Int)] effs
         => CodeQ Int -> CodeQ (Int -> m Int) -> Prog effs (CodeQ Int)
localGen cN self =
  do b <- split [|| $$cN > 0 ||]
     if b
       then local @(CodeQ Int) (\r -> [|| $$r + 1 ||]) (up [|| $$self ($$cN - 1) ||])
       else ask @(CodeQ Int)

pythGen :: forall effs m. Members '[CodeGen, Choose, Empty, UpOp m] effs
        => CodeQ Int -> CodeQ (Int -> m Int) -> Prog effs (CodeQ (Int, Int, Int))
pythGen cN cChoose = 
  do x <- up ([|| $$cChoose $$cN||])
     y <- up ([|| $$cChoose $$cN||])
     z <- up ([|| $$cChoose $$cN||])
     genIf [|| $$x * $$x + $$y * $$y == $$z * $$z ||] 
       (return [|| ($$x, $$y, $$z) ||])
       empty

chooseGen :: forall effs m. Members '[CodeGen, Choose, Empty, UpOp m] effs
        => CodeQ Int -> CodeQ (Int -> m Int) -> Prog effs (CodeQ Int)
chooseGen cN self =
  genIf [|| $$cN > 0 ||]
    (up [|| $$self ($$cN - 1) ||] <|> return cN)
    empty

coroutine1Gen :: forall effs m. Members '[CodeGen, Yield (CodeQ Int) (CodeQ Int), UpOp m] effs
              => CodeQ [Int] -> CodeQ ([Int] -> m [Int]) -> Prog effs (CodeQ [Int])
coroutine1Gen cXs self =
  do genCase cXs \case
       Nothing         -> return [|| [] ||]
       Just (cX, cXs') ->
         do cY <- yield @(CodeQ Int) @(CodeQ Int) cX
            rs <- up [|| $$self $$cXs' ||]
            return [|| $$cY : $$rs ||]

coroutine2Gen :: forall effs m a. Members '[CodeGen, Yield (CodeQ Int) (CodeQ Int), UpOp m] effs
              => CodeQ Int -> CodeQ (Int -> m a) -> Prog effs (CodeQ a)
coroutine2Gen cA self =
  do cB <- yield [|| $$cA + 100 ||]
     up [|| $$self $$cB ||]
