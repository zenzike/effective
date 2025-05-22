{-|
Module      : Control.Effect.CodeGen.Split
Description : Generate case splits of object-level values
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains a typeclass `Split a b` with a member function  
@`genSplit :: Up a -> Gen b`@ for generating a case split of the object
level @a@-value and resulting in a @b@-value at meta-level in the 
code-generation monad.
-}
{-# LANGUAGE FunctionalDependencies, BlockArguments, TemplateHaskell #-}
module Control.Effect.CodeGen.Split where

import Control.Monad.Trans.YRes (YStep(..))
import Control.Monad.Trans.CRes (CStep(..))
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Gen
import Control.Effect 

-- | Generate a pattern matching of the @a@-value (into a view of type @b@) and continue 
-- the code generation in all branches.
-- The instances are rather mundane and we may generate them generically in the future.
class Split a b | a -> b, b -> a where
  genSplit :: Up a -> Gen b

-- | Split operation for meta-programs.
split :: (Member CodeGen sig, Split a b) => Up a -> Prog sig b 
split = liftGen . genSplit

-- | With the extension LambdaCase, a useful pattern in meta-programs is
--
-- > genCase a $ \case
-- >   P1 -> ...
-- >   P2 -> ...
-- 
-- where @a :: Up a@ is a piece of code that splittable.
genCase :: (Member CodeGen sig, Split a b) => Up a -> (b -> Prog sig c) -> Prog sig c
genCase ua k = split ua >>= k 

instance Split Bool Bool where 
  genSplit cb = Gen \k -> [|| if $$cb then $$(k True) else $$(k False) ||]

-- | Meta-level if-then-else.
genIf :: (Member CodeGen sig) => Up Bool -> Prog sig c -> Prog sig c -> Prog sig c
genIf uc t e = genCase uc (\b -> if b then t else e)

instance Split (a,b) (Up a, Up b) where
  genSplit cab = Gen \k -> [|| case $$cab of (a, b) -> $$(k ([||a||], [||b||])) ||]

instance Split [a] (Maybe (Up a, Up [a])) where
  genSplit cl = Gen \k -> [|| 
    case $$cl of
       []   -> $$(k Nothing)
       a:as -> $$(k (Just ([||a||], [||as||]))) ||]

instance Split (Maybe a) (Maybe (Up a)) where
  genSplit cmb = Gen \k -> [||
    case $$cmb of
      Nothing -> $$(k Nothing)
      Just a  -> $$(k (Just [||a||])) ||]

instance Split (Either a b) (Either (Up a) (Up b)) where
  genSplit ce = Gen \k -> [|| 
    case $$ce of
      Left  a -> $$(k (Left [|| a ||]))
      Right b -> $$(k (Right [|| b ||])) ||]

instance Split (YStep a b x) (YStep (Up a) (Up b) (Up x)) where
  genSplit cy = Gen \k -> [||
    case $$cy of
      YieldS a f -> $$(k (YieldS [||a||] (\cb -> [|| f $$cb ||])))  
    ||]

instance Split (CStep a x) (CStep (Up a) (Up x)) where
  genSplit cc = Gen \k -> [|| 
    case $$cc of
      FailS       -> $$(k FailS)
      ChoiceS l r -> $$(k (ChoiceS [||l||] [||r||]))
      ActS a x    -> $$(k (ActS [||a||] [||x||]))
    ||]