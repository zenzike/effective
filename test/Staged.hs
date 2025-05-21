{-# LANGUAGE BlockArguments, TemplateHaskell, ImpredicativeTypes, LambdaCase, TypeFamilies #-}
module Main where

import Control.Effect
import Control.Effect.CodeGen
import Control.Effect.State.Strict
import Control.Effect.Nondet
import qualified Control.Effect.Maybe as Mb
import Control.Effect.Concurrency
import Control.Effect.Yield
import Control.Effect.Family.Scoped
import Control.Effect.Family.Algebraic
import Data.Functor.Identity
import Control.Effect.Internal.AlgTrans
import qualified Control.Monad.Trans.State.Strict as S

import StagedGen
import Control.Effect.Except
import Control.Monad.Trans.Push
import Control.Monad.Trans.List
import Control.Monad.Trans.YRes
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.List.Kind
import Control.Monad (join)

{-
Generated code: 
    StateT
      (\ s_a4dv
         -> Identity
              (if (s_a4dv > 0) then
                   let x_a4dw = (s_a4dv + 1)
                   in
                     case runIdentity (runStateT countdown x_a4dw) of
                       (a_a4dx, b_a4dy) -> (a_a4dx, b_a4dy)
               else
                   ((), s_a4dv)))
-}

countdown :: StateT Int Identity ()
countdown = $$(stage 
  (letPut @Int 
  `fuseAT` upState @Int @Identity 
  `fuseAT` stateAT @(Up Int)) 
  (countdownGen [|| countdown ||]))

{-
Generated code:
    ExceptT
      (Identity
         (if (n_a4nE > 0) then
              case runIdentity (runExceptT (catchProgram (n_a4nE - 1))) of
                Left a_a4Uc -> Left ()
                Right b_a4Ud -> Right b_a4Ud
          else
              Left ()))
-}

catchProgram :: Int -> ExceptT () Identity ()
catchProgram n = $$(stage
  (upExcept @() @Identity `fuseAT` exceptAT @(Up ())) 
  (catchGen [||n||] [||catchProgram||]))
        

{-
The code generator catchGen can be used for generating different types of programs:

    StateT
      (\ s_a5aI
         -> ExceptT
              (Identity
                 (if (n_a4ph > 0) then
                      case runIdentity (runExceptT (catchProgram (n_a4ph - 1))) of
                        Left a_a5aJ -> Left ()
                        Right b_a5aK -> Right (b_a5aK, s_a5aI)
                  else
                      Left ())))

-}
catchProgram2 :: Int -> StateT Int (ExceptT () Identity) ()
catchProgram2 n = $$(stage
    ( upState @Int @(ExceptT () Identity)
      `fuseAT` upExcept @() @Identity 
      `fuseAT` stateAT @(Up Int) 
      `fuseAT` exceptAT @(Up ())) 
    (catchGen [||n||] [||catchProgram||]))

-- foldr (\ a_a56k ms_a56l -> (a_a56k : ms_a56l)) [] as_a4qa
listExample :: [a] -> [a]
listExample as = $$(stage 
  (pushUpAT @Identity)
  (up [||as||]))

-- Generated code: as_a4XQ
listExample' :: [a] -> [a]
listExample' as = $$(downJoin $ 
  evalGen 
  (pushUpAT @Identity)
  (return [||as||]))


-- foldr (\ a_a57X ms_a57Y -> ((a_a57X + 1) : ms_a57Y)) [] as_a4qu
listExample2 :: [Int] -> [Int]
listExample2 as = $$(stage
  (pushUpAT @Identity) 
  do i <- up [||as||]
     return ([||$$i + 1||]))

{-
    foldr
      (\ a_a3KU ms_a3KV
         -> foldr
              (\ a_a3KW ms_a3KX -> ((a_a3KU + a_a3KW) : ms_a3KX)) ms_a3KV
              as_a1BF)
      [] as_a1BF
-}
listExample3 :: [Int] -> [Int]
listExample3 as = $$(stage (pushUpAT @Identity) $ 
  do i <- up [||as||]
     j <- up [||as||]
     return ([||$$i + $$j||]))


{- The following even does fold fusion automatically.
    foldr
      (\ a_a6Sk ms_a6Sl
         -> foldr
              (\ a_a6Sm ms_a6Sn -> ((f_a5Y3 a_a6Sk + g_a5Y4 a_a6Sm) : ms_a6Sn))
              ms_a6Sl as_a5Y5)
      [] as_a5Y5
-}
listExample4 :: (Int -> Int) -> (Int -> Int) -> [Int] -> [Int]
listExample4 f g as = $$(stage (pushUpAT @Identity) $ 
  do i <- fmap (\i -> [|| f $$i ||]) (up [||as||])
     j <- fmap (\i -> [|| g $$i ||]) (up [||as||])
     return ([||$$i + $$j||]))
     

{-
Generated code (manually reformatted -- the indentation may be broken):

ListT (StateT (\ s_a62N -> Identity (
  let x_a62O = runIdentity (runStateT (
    let cons_a62Q = \ a_a62R ms_a62S ->
        StateT (\ s_a62T -> Identity
          (let x_a62U = runIdentity (runStateT 
            (let cons_a62W = \ a_a62X ms_a62Y -> StateT (\ s_a62Z -> 
                Identity (let x_a630 = runIdentity (runStateT ms_a62Y (a_a62R * a_a62X))
                          in case x_a630 of
                            (a_a631, b_a632) -> (Just (((s_a62N + a_a62R) + a_a62X), ListT (return a_a631)), b_a632)))
                  nil_a62V = StateT (\ s_a633 -> Identity 
                    (let x_a634 = runIdentity (runStateT ms_a62S s_a633)
                    in case x_a634 of 
                      (a_a635, b_a636) -> (a_a635, b_a636)))
            in foldListT cons_a62W nil_a62V as_a5jb) s_a62T)
          in case x_a62U of (a_a637, b_a638) -> (a_a637, b_a638)))
          nil_a62P = StateT (\ s_a639 -> Identity (Nothing, s_a639))
      in foldListT cons_a62Q nil_a62P as_a5jb) s_a62N)
  in case x_a62O of (a_a63a, b_a63b) -> (a_a63a, b_a63b))))
-}
listExample5 :: ListT (StateT Int Identity) Int -> ListT (StateT Int Identity) Int
listExample5 as = $$(stage 
  (pushUpAT @(StateT Int Identity) 
  `fuseAT` upState @Int @Identity
  `fuseAT` stateAT @(Up Int)) $ 
  do s <- get
     i <- up [||as||]
     j <- up [||as||]
     put [|| $$i * $$j ||]
     return ([||$$s + $$i + $$j||]))


{-
    ListT
      (Identity
         (if (n_a5YZ > 0) then
              runIdentity
                (foldListT
                   (\ a_a6JH ms_a6JI
                      -> Identity (Just (a_a6JH, ListT (return (runIdentity ms_a6JI)))))
                   (Identity (Just (n_a5YZ, ListT (return Nothing))))
                   (choice (n_a5YZ - 1)))
          else
              Nothing))
-}
choice :: Int -> ListT Identity Int
choice n = $$(stage (pushUpAT @Identity) $
  choiceGen [||n||] [|| choice ||])

{-
    if (n_a1sJ > 0) then
        runIdentity
          (foldr
             (\ a_a4Ex ms_a4Ey -> Identity (a_a4Ex : runIdentity ms_a4Ey))
             (Identity (n_a1sJ : [])) (choice' (n_a1sJ - 1)))
    else
        []
-}
choice' :: Int -> [Int]
choice' n = $$(stage (pushUpAT @Identity) $
  choiceGen [||n||] [|| choice' ||])


{-
  StateT
      (\ s_a6QG
         -> ListT
              (Identity
                 (if (n_a60H > 0) then
                      runIdentity
                        (foldListT
                           (\ a_a6QH ms_a6QI
                              -> Identity
                                   (Just ((a_a6QH, s_a6QG), ListT (return (runIdentity ms_a6QI)))))
                           (Identity (Just ((n_a60H, s_a6QG), ListT (return Nothing))))
                           (choice (n_a60H - 1)))
                  else
                      Nothing)))
-}
choiceST :: Int -> StateT Int (ListT Identity) Int
choiceST n = $$(stage
  (stateAT @(Up Int) `fuseAT` pushUpAT @Identity)
  (choiceGen [||n||] [|| choice ||]))

{-
    StateT
      (\ s_a6kt
         -> do x_a6ku <- putStrLn "Hello"
               if (s_a6kt > 0) then
                   do x_a6kv <- runStateT ioExample (s_a6kt - 1)
                      case x_a6kv of (a_a6kw, b_a6kx) -> return (a_a6kw, b_a6kx)
               else
                   return ((), s_a6kt))
-}
ioExample :: StateT Int IO ()
ioExample = $$(stageM (Proxy @IO)
  (upState @Int @IO `fuseAT` stateAT @(Up Int))
  (ioProg [|| ioExample ||]))

{-
    StateT
      (\ s_a6JU
         -> do x_a6JV <- putStrLn "Hello"
               if (s_a6JU > 0) then
                   runStateT ioExample (s_a6JU - 1)
               else
                   return ((), s_a6JU))
-}
ioExample2 :: StateT Int IO ()
ioExample2 = $$(downTail $
  evalGenM @IO (upState @Int @IO `fuseAT` stateAT @(Up Int))
    (do up [|| putStrLn "Hello" ||]
        s <- get @(Up Int)
        b <- split [|| $$s > 0 ||]
        if b then put [|| $$s - 1||] >> return (Right [|| ioExample ||])
             else return (Left [||()||])))

{-
StateT (\ s_abe7 -> 
  do x_abe8 <- putStrLn "Hello"
            runStateT (StateT
                (\ s_abe9 -> runStateT (StateT
                            (\ s_abea
                              -> if (s_abe9 > 0) then
                                      runStateT
                                        (StateT
                                          (\ s_abeb
                                              -> runStateT
                                                  (do a_abec <- ioExample
                                                      return a_abec)
                                                  (s_abe9 - 1)))
                                        s_abea
                                  else
                                      runStateT
                                        (StateT (\ s_abed -> return ((), s_abed))) s_abea))
                        s_abe9))
              s_abe7)
-}
ioExample3 :: StateT Int IO ()
ioExample3 = $$(stageM (Proxy @IO) 
    (upCache @(StateT Int IO) `fuseAT` upState @Int @IO `fuseAT` stateAT @(Up Int))
    (do up [|| putStrLn "Hello" ||]
        s <- get @(Up Int)
        b <- split [|| $$s > 0 ||]
        if b then put [|| $$s - 1||] >> up [|| ioExample ||] 
             else return [||()||]))

{-
    StateT
      (\ s_abeg
         -> do x_abeh <- putStrLn "Hello"
               if (s_abeg > 0) then
                   runStateT
                     (do a_abei <- ioExample
                         StateT (\ s_abej -> return (a_abei, s_abej)))
                     (s_abeg - 1)
               else
                   return ((), s_abeg))
-}
ioExample4 :: StateT Int IO ()
ioExample4 = $$(stageM (Proxy @IO) 
    (upFree @(StateT Int IO) `fuseAT` upState @Int @IO `fuseAT` stateAT @(Up Int))
    (do up [|| putStrLn "Hello" ||]
        s <- get @(Up Int)
        b <- split [|| $$s > 0 ||]
        if b then put [|| $$s - 1||] >> up [|| ioExample ||] 
             else return [||()||]))

{-
  StateT (\ s_abTh ->
    do x_abTi <- putStrLn "Hello"
       if (s_abTh > 0) then
           runStateT ioExample (s_abTh - 1)
       else
           return ((), s_abTh))
-}
ioExample5 :: StateT Int IO ()
ioExample5 = $$(stageM (Proxy @IO) 
  (upCache @(StateT Int IO) 
  `fuseAT` upState @Int @IO 
  `fuseAT` stateAT @(Up Int))
  (ioProg [|| ioExample ||]))


{-
    StateT
      (\ s_a6AM
         -> MaybeT
              (Identity
                 (if b_a56x then
                      let x_a6AN = 10 :: Int in
                      let x_a6AO = (x_a6AN + x_a6AN) in Just ((), x_a6AO)
                  else
                      let x_a6AP = 20 :: Int in
                      let x_a6AQ = (x_a6AP + x_a6AP) in Just ((), x_a6AQ))))
-}
joinEx :: Bool -> StateT Int (MaybeT Identity) ()
joinEx b = $$(stage
  (letPut @Int `fuseAT` stateAT @(Up Int) `fuseAT` Mb.exceptAT)
  (noJoinProg [||b||]))


{-
    StateT (\ s_a4UP -> MaybeT (Identity 
      (case runIdentity (runStateT (StateT
         (\ s_a4UQ -> Identity
            (if b_a1Bc then
               let x_a4UR = 10 :: Int in ((), x_a4UR)
             else
               let x_a4US = 20 :: Int in ((), x_a4US))) ) s_a4UP)
       of (a_a4UT, b_a4UU)
           -> let x_a4UV = (b_a4UU + b_a4UU) in Just ((), x_a4UV))))
-}



{-
    StateT (\ s_a9w9 -> MaybeT (Identity
                 (let x_a9wa = StateT (\ s_a9wb -> MaybeT (Identity
                                     (if b_a7bw then
                                          let x_a9wc = 10 :: Int in Just ((), x_a9wc)
                                      else
                                          let x_a9wd = 20 :: Int in Just ((), x_a9wd))))
                  in
                    case runIdentity (runMaybeT (runStateT x_a9wa s_a9w9)) of
                      Nothing -> Nothing
                      Just a_a9we
                        -> case a_a9we of
                             (a_a9wf, b_a9wg)
                               -> let x_a9wh = (b_a9wg + b_a9wg) in Just ((), x_a9wh))))
-}
joinEx1 :: Bool -> StateT Int (MaybeT Identity) ()
joinEx1 b = $$(stage
  (letPut @Int 
     `fuseAT` resetAT' @(StateT Int (MaybeT Identity))
     `fuseAT` weakenC @((~) Gen) (upState @Int @(MaybeT Identity)
     `fuseAT` stateAT @(Up Int) 
     `fuseAT` upMaybe @Identity
     `fuseAT` Mb.exceptAT))
  (resetProg [||b||]))
{-
The in the code above, `weakenCAnd @Monad` is for overcoming a bug (or limitation?)
of the extension UndecidableSuperClasses. Without it we would get an error report:

> Could not deduce ‘Monad m’
>     arising from the head of a quantified constraint
>     arising from a use of ‘fuseAT’
>   from the context: CompC
>                       [StateT (Up Int), MaybeT]
>                       ((<~$) (StateT Int (MaybeT Identity)))
>                       (CompC
>                          [StateT (Up Int), MaybeT]
>                          Monad
>                          (CompC '[MaybeT] Monad (CompC '[MaybeT] Monad Monad)))
>                       m

although `Monad m` /is/ implied by this big `CompC` constraint. I suspect that this
is because `CompC` is defined using UndecidableSuperClasses and GHC only expands
CompC up until a fixed step, so it failed to see that `Monad m` is implied. We
overcome this by using `weakenC` to replace the above big @CompC@ constraint
with the simpler and stronger constraint @(~) Gen@. 

Alternatively, we can use the combinator `fuseAT'` that keeps the constraints simple.
-}

joinEx1' :: Bool -> StateT Int (MaybeT Identity) ()
joinEx1' b = $$(stage
  (letPut @Int 
     `fuseAT'` resetAT' @(StateT Int (MaybeT Identity))
     `fuseAT`  upState @Int @(MaybeT Identity)
     `fuseAT'` upMaybe @Identity
     `fuseAT'` stateAT @(Up Int) 
     `fuseAT'` Mb.exceptAT)
  (resetProg [||b||]))


{-
    StateT
      (\ s_aaCD
         -> MaybeT
              (Identity
                 (let x_aaCE = \ _ -> Nothing in
                  let
                    x_aaCF
                      = \ x_aaCG -> let x_aaCH = (x_aaCG + x_aaCG) in Just ((), x_aaCH)
                  in
                    if b_a8t9 then
                        let x_aaCI = 10 :: Int in x_aaCF x_aaCI
                    else
                        let x_aaCJ = 20 :: Int in x_aaCF x_aaCJ)))
-}
joinEx2 :: Bool -> StateT Int (MaybeT Identity) ()
joinEx2 b = $$(down $ evalTr' 
  (letPut @Int 
  `fuseAT'` upState @Int @Identity 
  `fuseAT'` stateAT @(Up Int)
  `fuseAT'` Mb.exceptAT
  `fuseAT'` asAT (genAlg # joinGenAlg))
  (joinProg [||b||]))


{-
    StateT (\ s_a9UB -> ListT (MaybeT (Identity
                    (let x_a9UC = MaybeT (Identity (Just Nothing)) in
                     let
                       x_a9UD = \ x_a9UE -> \ rest_a9UF -> MaybeT (Identity
                         (let x_a9UG = (x_a9UE + x_a9UE)
                          in
                            case runIdentity (runMaybeT rest_a9UF) of
                              Nothing -> Nothing
                              Just a_a9UH
                                -> Just
                                     (Just (((), x_a9UG), ListT (return a_a9UH)))))
                     in
                       if b_a7br then
                           let x_a9UI = 10 :: Int in
                           let x_a9UJ = x_a9UD x_a9UI (MaybeT (Identity
                              (case runIdentity (runMaybeT x_a9UC) of
                                 Nothing -> Nothing
                                 Just a_a9UK -> Just a_a9UK)))
                           in
                             case runIdentity (runMaybeT x_a9UJ) of
                               Nothing -> Nothing
                               Just a_a9UL -> Just a_a9UL
                       else
                           let x_a9UM = 20 :: Int in
                           let x_a9UN = x_a9UD x_a9UM
                                   (MaybeT
                                      (Identity
                                         (case runIdentity (runMaybeT x_a9UC) of
                                            Nothing -> Nothing
                                            Just a_a9UO -> Just a_a9UO)))
                           in
                             case runIdentity (runMaybeT x_a9UN) of
                               Nothing -> Nothing
                               Just a_a9UP -> Just a_a9UP))))

-- there are some unnecessary eta-expansion of @MaybeT Identity@ generated by 
-- @up . down@. Can we optimise this out?
-- Yes, using @upCache@ like below.
-}
joinEx3 :: Bool -> StateT Int (ListT (MaybeT Identity)) ()
joinEx3 b = $$(down $ evalTr' 
  (letPut @Int 
  `fuseAT'` stateAT @(Up Int)
  `fuseAT'` caseATSameC' (joinPush @(MaybeT Identity)) 
                         (weakenOEffs pushUpAT)
  `fuseAT'` upMaybe @Identity
  `fuseAT'` (hideAT @'[Mb.Catch] Mb.exceptAT)
  `fuseAT'` asAT genAlg)
  (joinProg [||b||]))

{-
    StateT
      (\ s_a7gX -> ListT (MaybeT
                 (let x_a7gY = MaybeT (Identity (Just Nothing)) in
                  let x_a7gZ = \ x_a7h0 -> \ rest_a7h1
                               -> MaybeT
                                    (let x_a7h2 = (x_a7h0 + x_a7h0)
                                     in
                                       case runIdentity (runMaybeT rest_a7h1) of
                                         Nothing -> Identity Nothing
                                         Just a_a7h3
                                           -> Identity (Just (Just (((), x_a7h2), ListT (return a_a7h3)))))
                  in
                    if b_a2bj then
                        let x_a7h4 = 10 :: Int in
                        let x_a7h5 = x_a7gZ x_a7h4 (MaybeT (runMaybeT x_a7gY))
                        in runMaybeT x_a7h5
                    else
                        let x_a7h6 = 20 :: Int in
                        let x_a7h7 = x_a7gZ x_a7h6 (MaybeT (runMaybeT x_a7gY))
                        in runMaybeT x_a7h7)))

-}
joinEx4 :: Bool -> StateT Int (ListT (MaybeT Identity)) ()
joinEx4 b = $$(down $ evalTr' 
  (letPut @Int 
  `fuseAT'` stateAT @(Up Int)
  `fuseAT'` caseATSameC' (joinPush @(MaybeT Identity)) 
                         (weakenOEffs pushUpAT)
  `fuseAT'` upCache @(MaybeT Identity)
  `fuseAT'` upMaybe @Identity
  `fuseAT'` (hideAT @'[Mb.Catch] Mb.exceptAT)
  `fuseAT'` asAT genAlg)
  (joinProg [||b||]))


{-
reset :: Gen (Up a) -> Gen (Up a)
reset = return . runGen

shift :: (forall b. (Up a -> Up b) -> Gen (Up b)) -> Gen (Up a)
shift f = Gen $ runGen . f
-}

testShift :: Up (Identity Int)
testShift = down $ 
  do c <- resetGen (do ci <- shiftGen (\k -> do b' <- genLet_ (k [|| 5 ||])
                                                return (k [|| 0 ||]))
                       return [|| $$ci + $$ci ||])
     return ([|| $$c - 1 ||])



{-
    MaybeT
      (Identity
         (if b_a1C9 then
              if c_a1Ca then
                  let x_a4S2 = (0 + 0) in Just x_a4S2
              else
                  let x_a4S3 = (1 + 1) in Just x_a4S3
          else
              Nothing))
-}
testShift2 :: Bool -> Bool -> MaybeT Identity Int 
testShift2 b c = $$(down @(MaybeT Gen) $ 
  do b' <- lift (genSplit [||b||] )
     i <- case b' of 
       True -> 
         do c' <- lift (genSplit [||c||])
            case c' of
              True -> return [||0||]
              False -> return [||1||]
       False -> MaybeT (return Nothing)
     lift (genLet_ [|| $$i + $$i ||]))

{-
    MaybeT
      (Identity
         (let x_a4Ui = Nothing in
          let
            x_a4Uj = \ a_a4Uk -> let x_a4Ul = (a_a4Uk + a_a4Uk) in Just x_a4Ul
          in
            if b_a1CR then if c_a1CS then x_a4Uj 0 else x_a4Uj 1 else x_a4Ui))
-}
testShift3 :: Bool -> Bool -> MaybeT Identity Int 
testShift3 b c = $$(down @(MaybeT Gen) $ 
  do i <- mergeMb $ 
       do b' <- lift (genSplit [||b||] )
          case b' of 
            True -> 
              do c' <- lift (genSplit [||c||])
                 case c' of
                   True -> return [||0||]
                   False -> return [||1||]
            False -> MaybeT (return Nothing)
     lift (genLet_ [|| $$i + $$i ||]))

{-
    MaybeT
      (Identity
         (case
              let x_a7tg = Nothing in
              let
                x_a7th = \ a_a7ti -> let x_a7tj = (a_a7ti + a_a7ti) in Just x_a7tj
              in if b_a5Ix then if c_a5Iy then x_a7th 0 else x_a7th 1 else x_a7tg
          of
            Nothing -> Nothing
            Just a_a7tk -> let x_a7tl = (a_a7tk * a_a7tk) in Just x_a7tl))
-}
testShift4 :: Bool -> Bool -> MaybeT Identity Int 
testShift4 b c = $$(down @(MaybeT Gen) $ 
  do j <- resetMb (
       do i <- mergeMb $ 
            do b' <- lift (genSplit [||b||] )
               case b' of 
                 True -> 
                   do c' <- lift (genSplit [||c||])
                      case c' of
                        True -> return [||0||]
                        False -> return [||1||]
                 False -> MaybeT (return Nothing)
          lift (genLet_ [|| $$i + $$i ||]))
     lift (genLet_ [|| $$j * $$j ||]))


{-
ResT
  (if even i_a7G5 then
        let x_aass = (i_a7G5 `div` 2)
        in return (Right (YieldS x_aass (\ x_aast -> ResT (unResT (yieldEx x_aast)))))
    else
        let x_aasu = ((3 * i_a7G5) + 1)
        in return (Right (YieldS x_aasu (\ x_aasv -> ResT (unResT (yieldEx x_aasv))))))
-}
yieldEx:: Int -> YResT Int Int Identity Int
yieldEx 1 = return 1
yieldEx i = $$(stage
  (upCache @(YResT Int Int Identity) `fuseAT` yResUpAT @Identity @Int @Int)
  (yieldGen [|| yieldEx ||] [||i||]))

{-
    ResT
      (if even i_a2dO then
           let x_a6FO = (i_a2dO `div` 2)
           in return (Right (YieldS (x_a6FO + 1) (\ x_a6FP -> ResT (runIdentity
                                (foldRes
                                   (\ a_a6FQ -> Identity (unResT (return a_a6FQ)))
                                   (\ sm_a6FR -> Identity (case sm_a6FR of
                                              YieldS a_a6FS f_a6FT
                                                -> return (Right (YieldS (a_a6FS + 1)
                                                           (\ x_a6FU -> ResT (runIdentity (f_a6FT (x_a6FU - 1))))))))
                                   (yieldEx (x_a6FP - 1)))))))
       else
        --  ...
-}
yieldEx2:: Int -> YResT Int Int Identity Int
yieldEx2 1 = return 1
yieldEx2 i = $$(stage
  (upCache @(YResT Int Int Identity) `fuseAT` yResUpAT @Identity @Int @Int)
  (Control.Effect.Yield.mapYield
     ((\x -> [||$$x + 1||]) :: Up Int -> Up Int)
     ((\x -> [||$$x - 1||]) :: Up Int -> Up Int)
     (yieldGen [|| yieldEx ||] [||i||])))

{-
foldr (\ a_aaPR ms_aaPS -> (1 + ms_aaPS)) 0 xs_a7IH
-}
listExample6 :: [Int] -> Int
listExample6 xs = $$(runGen $
  runPushT (evalGen pushGen (do i <- up [||xs||]; return [||$$i + $$i||]))
    (\_ n -> do n' <- n; return [|| 1 + $$n' ||]) 
    (return [||0||]))

main = return ()