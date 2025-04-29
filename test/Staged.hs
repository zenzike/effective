{-# LANGUAGE BlockArguments, TemplateHaskell, ImpredicativeTypes #-}
module Main where

import Control.Effect
import Control.Effect.CodeGen
import Control.Effect.State.Strict
import Control.Effect.Nondet
import Control.Effect.Family.Scoped
import Control.Effect.Family.Algebraic
import Control.Effect.Internal.Forward.ForwardC
import Data.Functor.Identity
import Control.Effect.Internal.AlgTrans
import qualified Control.Monad.Trans.State.Strict as S

import StagedGen
import Control.Effect.Except
import Control.Monad.Trans.Push
import Control.Monad.Trans.List
import Control.Monad.Trans.Class
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
countdown = $$(down $ evalGen 
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
catchProgram n = $$(down $ evalGen 
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
catchProgram2 n = $$(down $ 
    evalGen
    ( upState @Int @(ExceptT () Identity)
      `fuseAT` upExcept @() @Identity 
      `fuseAT` stateAT @(Up Int) 
      `fuseAT` exceptAT @(Up ())) 
    (catchGen [||n||] [||catchProgram||]))

-- foldr (\ a_a56k ms_a56l -> (a_a56k : ms_a56l)) [] as_a4qa
listExample :: [a] -> [a]
listExample as = $$(down $ 
  evalGen 
  (pushAT @Identity)
  (up [||as||]))

-- Generated code: as_a4XQ
listExample' :: [a] -> [a]
listExample' as = $$(downJoin $ 
  evalGen 
  (pushAT @Identity)
  (return [||as||]))


-- foldr (\ a_a57X ms_a57Y -> ((a_a57X + 1) : ms_a57Y)) [] as_a4qu
listExample2 :: [Int] -> [Int]
listExample2 as = $$(down . evalGen (pushAT @Identity) $
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
listExample3 as = $$(down . evalGen (pushAT @Identity) $ 
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
listExample4 f g as = $$(down . evalGen (pushAT @Identity) $ 
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
listExample5 as = $$(down . evalGen 
  (pushAT @(StateT Int Identity) 
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
choice n = $$(down . evalGen (pushAT @Identity) $
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
choice' n = $$(down . evalGen (pushAT @Identity) $
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
choiceST n = $$(down $
  evalGen (stateAT @(Up Int) `fuseAT` pushAT @Identity)
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
ioExample = $$(down $
  evalGenM @IO (upState @Int @IO `fuseAT` stateAT @(Up Int))
    (do up [|| putStrLn "Hello" ||]
        s <- get @(Up Int)
        b <- split [|| $$s > 0 ||]
        if b then put [|| $$s - 1||] >> up [|| ioExample ||] 
             else return [||()||]))

{-
    StateT
      (\ s_a6u3
         -> do x_a6u4 <- putStrLn "Hello"
               if (s_a6u3 > 0) then
                   runStateT ioExample (s_a6u3 - 1)
               else
                   runStateT (return ()) s_a6u3)
-}
ioExample2 :: StateT Int IO ()
ioExample2 = $$(downJoin $
  evalGenM @IO (upState @Int @IO `fuseAT` stateAT @(Up Int))
    (do up [|| putStrLn "Hello" ||]
        s <- get @(Up Int)
        b <- split [|| $$s > 0 ||]
        if b then put [|| $$s - 1||] >> return [|| ioExample ||] 
             else return [||return ()||]))

main = return ()