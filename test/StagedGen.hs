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
import Control.Effect.Alternative
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

choiceGen :: forall sig m. Members '[CodeGen, UpOp m, Choose, Empty] sig
          => Up Int -> Up (Int -> m Int) -> Prog sig (Up Int)
choiceGen cN self =
  do b <- split [|| $$cN > 0 ||]
     if b
      then up [|| $$self ($$cN - 1) ||] <|> return cN
      else empty


mergeMb :: MaybeT Gen (Up a) -> MaybeT Gen (Up a)
mergeMb ma = shiftMb \kj kn -> runGen $
  do kN <- genLet_ [|| $$kn ||]
     kJ <- genLet_ [|| \a -> $$(kj ([||a||])) ||]
     m <- runMaybeT ma
     case m of
       Nothing -> return kN
       Just a  -> return ([|| $$kJ $$a ||])

shiftMb :: (forall r. (a -> Up r) -> Up r -> Up r)
        -> MaybeT Gen a
shiftMb f = MaybeT $ shiftGen \k -> return (f (k . Just) (k Nothing))

resetMb :: forall a. MaybeT Gen (Up a) -> MaybeT Gen (Up a)
resetMb g =
  let act :: Up (MaybeT Identity a)
      act = down g
  in MaybeT do genSplit [|| runIdentity (runMaybeT $$act) ||]

{-
shift :: (forall r. (a -> Up r) -> Gen (Up r)) -> Gen a
shift f = Gen $ runGen . f
-}

mergeST :: StateT (Up s) Gen (Up a) -> StateT (Up s) Gen (Up a)
mergeST ma = StateT \s -> shiftGen \k ->
  do k' <- genLet_ [|| \a s -> $$(k ([||a||], [||s||])) ||]
     (a, s) <- runStateT ma s
     return [|| $$k' $$a $$s ||]


mergePS :: PushT Gen (Up a) -> PushT Gen (Up a)
mergePS ma = PushT \kc kn ->
  do kn' <- genLet_ [|| runIdentity $$(down kn) ||]
     kc' <- genLet_ [|| \a t -> runIdentity $$(down (kc [||a||] (return [||runIdentity t||]))) ||]
     runPushT ma (\ca mas -> return [|| $$kc' $$ca $$(down mas) ||]) (return kn')

noJoinProg :: (Members '[Put (Up Int), Get (Up Int), Mb.Throw, Mb.Catch, CodeGen] sig)
         => Up Bool -> Prog sig (Up ())
noJoinProg b =
  do genCase b (\case
         True  -> putUp [|| 10 :: Int ||]
         False -> putUp [|| 20 :: Int ||])
     s <- getUp @Int
     put [|| $$s + $$s ||]
     return [|| () ||]

resetProg :: (Members '[Put (Up Int), Get (Up Int), Mb.Throw, Mb.Catch, CodeGen, Reset] sig)
         => Up Bool -> Prog sig (Up ())
resetProg b =
  do reset $ genCase b (\case
         True  -> putUp [|| 10 :: Int ||] >> return [||()||]
         False -> putUp [|| 20 :: Int ||] >> return [||()||])
     s <- getUp @Int
     put [|| $$s + $$s ||]
     return [|| () ||]

joinProg :: (Members '[Put (Up Int), Get (Up Int), Mb.Throw, CodeGen, JoinFlow] sig)
         => Up Bool -> Prog sig (Up ())
joinProg b =
  do joinFlow $ genCase b (\case
         True  -> putUp [|| 10 :: Int ||]
         False -> putUp [|| 20 :: Int ||])
     s <- getUp @Int
     put [|| $$s + $$s ||]
     return [|| () ||]


ioProg :: Members '[UpOp IO, UpOp m, CodeGen, Put (Up Int), Get (Up Int)] sig
       => Up (m ()) -> Prog sig (Up ())
ioProg self =
  do up [|| putStrLn "Hello" ||]
     s <- get @(Up Int)
     b <- split [|| $$s > 0 ||]
     if b then put [|| $$s - 1||] >> up self
          else return [||()||]

yieldGen :: Members '[Yield (Up Int) (Up Int), CodeGen, UpOp m] sig
         => Up (Int -> m Int) -> Up Int -> Prog sig (Up Int)
yieldGen self i =
  do i' <- split [|| even $$i ||] >>= \case
        True -> genLet [|| $$i `div` 2 ||]
        _    -> genLet [|| 3 * $$i + 1 ||]
     i'' <- yield i'
     up [|| $$self $$i'' ||]
     

-- The following programs are the tests from the heftia benchmark
--
catchGen :: forall sig m. Members '[CodeGen, UpOp m, Catch (Up ()), Throw (Up ())] sig 
         => Up Int -> Up (Int -> m ()) -> Prog sig (Up ())
catchGen cN self = 
  do b <- split [|| $$cN > 0 ||]
     if b 
      then catch (up [|| $$self ($$cN - 1)||]) (\(_ :: Up ()) -> throw @(Up ()) [||()||])
      else throw @(Up ()) [|| () ||]

countdownGen :: Members '[CodeGen, UpOp m, Put (Up Int), Get (Up Int)] sig 
             => Up (m ()) -> Prog sig (Up ())
countdownGen self = 
  do cs <- get @(Up Int)
     b <- split [|| $$cs > 0 ||]
     if b then do put [|| $$cs - 1 ||]; up self
          else return [|| () ||]

localGen :: forall sig m. Members '[CodeGen, UpOp m, Ask (Up Int), Local (Up Int)] sig
         => Up Int -> Up (Int -> m Int) -> Prog sig (Up Int)
localGen cN self =
  do b <- split [|| $$cN > 0 ||]
     if b
       then local @(Up Int) (\r -> [|| $$r + 1 ||]) (up [|| $$self ($$cN - 1) ||])
       else ask @(Up Int)

pythGen :: forall sig m. Members '[CodeGen, Choose, Empty, UpOp m] sig
        => Up Int -> Up (Int -> m Int) -> Prog sig (Up (Int, Int, Int))
pythGen cN cChoose = 
  do x <- up ([|| $$cChoose $$cN||])
     y <- up ([|| $$cChoose $$cN||])
     z <- up ([|| $$cChoose $$cN||])
     genIf [|| $$x * $$x + $$y * $$y == $$z * $$z ||] 
       (return [|| ($$x, $$y, $$z) ||])
       empty

chooseGen :: forall sig m. Members '[CodeGen, Choose, Empty, UpOp m] sig
        => Up Int -> Up (Int -> m Int) -> Prog sig (Up Int)
chooseGen cN self =
  genIf [|| $$cN > 0 ||]
    (up [|| $$self ($$cN - 1) ||] <|> return cN)
    empty 
    
coroutine1Gen :: forall sig m. Members '[CodeGen, Yield (Up Int) (Up Int), UpOp m] sig
              => Up [Int] -> Up ([Int] -> m [Int]) -> Prog sig (Up [Int])
coroutine1Gen cXs self =
  do genCase cXs \case
       Nothing         -> return [|| [] ||]
       Just (cX, cXs') -> 
         do cY <- yield @(Up Int) @(Up Int) cX
            rs <- up [|| $$self $$cXs' ||]
            return [|| $$cY : $$rs ||]

coroutine2Gen :: forall sig m a. Members '[CodeGen, Yield (Up Int) (Up Int), UpOp m] sig
              => Up Int -> Up (Int -> m a) -> Prog sig (Up a)
coroutine2Gen cA self = 
  do cB <- yield [|| $$cA + 100 ||]
     up [|| $$self $$cB ||]
