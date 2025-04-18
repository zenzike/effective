{-# LANGUAGE FunctionalDependencies, BlockArguments, TemplateHaskell #-}
module Control.Effect.CodeGen.Split where

import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Gen
import Control.Effect 

-- | Generate a pattern matching of the @a@-value (into a view of type @b@) and continue 
-- the code generation in all branches.
-- The instances are rather mundane and we may generate them generically in the future.
class Split a b | a -> b where
  genSplit :: Up a -> Gen b

{-# INLINE split #-}
split :: (Member LiftGen sig, Split a b) => Up a -> Prog sig b 
split = liftGen . genSplit

{-# INLINE caseM #-}
caseM :: (Member LiftGen sig, Split a b) => Up a -> (b -> Prog sig c) -> Prog sig c
caseM ua k = split ua >>= k 

instance Split Bool Bool where 
  genSplit cb = Gen \k -> [|| if $$cb then $$(k True) else $$(k False) ||]

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