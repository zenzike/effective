{-# LANGUAGE BlockArguments, TemplateHaskell, ImpredicativeTypes #-}
module Main where

import Control.Effect
import Control.Effect.CodeGen
import Control.Effect.State.Strict
import Control.Effect.Nondet
import Control.Effect.Internal.Handler.LowLevel
import Control.Effect.Internal.Handler.Type
import Control.Effect.Internal.Forward.ForwardC
import qualified Control.Monad.Trans.State.Strict as S

import StagedGen
import Control.Effect.Except
import Control.Monad.Trans.Push
import Control.Monad.Trans.List
import Control.Monad.Trans.Class

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
countdown = $$(down $ StateT \cs -> fmap (\(s,a) -> (a,s)) $ 
  handleM genAlg 
    (letPut @Int |> upStateStrict @Int @Identity |> state @(Up Int) cs) 
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
catchProgram n = $$(down $ ExceptT $ 
  handleM genAlg 
          (upExcept @() @Identity |> except) 
          (catchGen [||n||] [||catchProgram||]))
        

{-
Because of effective, the code generator catchGen can be used for generating different types
of programs:

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
catchProgram2 n = $$(down $ StateT \cs -> ExceptT $ fmap (fmap (\(s,a) -> (a,s))) $ 
  handleM genAlg 
    (upStateStrict @Int @(ExceptT () Identity) 
      |> upExcept @() @Identity 
      |> state @(Up Int) cs 
      |> except) 
    (catchGen [||n||] [||catchProgram||]))

-- foldr (\ a_a56k ms_a56l -> (a_a56k : ms_a56l)) [] as_a4qa
listExample :: [a] -> [a]
listExample as = $$(downLG $ upLG [||as||])

-- foldr (\ a_a57X ms_a57Y -> ((a_a57X + 1) : ms_a57Y)) [] as_a4qu
listExample2 :: [Int] -> [Int]
listExample2 as = $$(downLG $ do i <- upLG [||as||]; return ([||$$i + 1||]))

{-
    foldr
      (\ a_a3KU ms_a3KV
         -> foldr
              (\ a_a3KW ms_a3KX -> ((a_a3KU + a_a3KW) : ms_a3KX)) ms_a3KV
              as_a1BF)
      [] as_a1BF
-}
listExample3 :: [Int] -> [Int]
listExample3 as = $$(downLG $ 
  do i <- upLG [||as||]
     j <- upLG [||as||]
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
listExample4 f g as = $$(downLG $ 
  do i <- fmap (\i -> [|| f $$i ||]) (upLG [||as||])
     j <- fmap (\i -> [|| g $$i ||]) (upLG [||as||])
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
listExample5 as = $$(down $ 
  do s <- lift S.get
     i <- upPS [||as||]
     j <- upPS [||as||]
     lift (S.put [|| $$i * $$j ||])
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
choice n = $$(down $
  evalTr genAlg (withFwdsSameC @'[CodeGen] (weakenOEffs @'[CodeGen, UpOp Identity] (pushAT @Identity)))  
    (choiceGen [||n||] [|| choice ||]))


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
  evalTr genAlg  
    (fuseAT (stateAT @(Up Int))
            (withFwdsSameC @'[CodeGen] 
              (weakenOEffs @'[CodeGen, UpOp Identity] 
              (pushAT @Identity))))
    (choiceGen [||n||] [|| choice ||]))

choiceST' :: Int -> StateT Int (ListT Identity) Int
choiceST' n = $$(down $
  evalTr'
    (stateAT @(Up Int) 
      `fuseAT` pushAT 
      `fuseAT` asAT genAlg)
    (choiceGen [||n||] [|| choice ||]))

main = return ()