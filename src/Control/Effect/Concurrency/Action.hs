module Control.Effect.Concurrency.Action where

-- | A typeclass for types that can serve as actions in the style
-- of _algebra of communicating processes_ (ACP). 
class Eq a => Action a where
  -- `merge a b = Nothing` means the two actions `a` and `b` don't interact
  merge :: a -> a -> Maybe a

-- | Asymmetric actions in the style of Calculus for Communicating Systems (CCS)
data CCSAction a = Silent a | Action a | CoAction a deriving (Show, Eq)

instance Eq a => Action (CCSAction a) where
  merge (Action a) (CoAction b)
    | a == b    = Just (Silent a)
    | otherwise = Nothing
  merge _ _ = Nothing

dualAction :: CCSAction a -> CCSAction a
dualAction (Action a)   = CoAction a
dualAction (CoAction a) = Action a 
dualAction (Silent a)   = Silent a