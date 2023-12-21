{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Nondet where

import Control.Effect
import Control.Effect.Nondet
import Control.Effect ( Members, Prog, Prog' )
import Control.Effect.Nondet ( Stop, Or, or, list, stop )
import Data.List (sort)

import Control.Monad.Trans.Class

import Prelude hiding (or)

import Hedgehog ( MonadGen, Property, property, discover, Group, (===), forAll )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

tree :: Prog' '[Or, Stop] Int
tree = or (or (return 1)
              (or (return 3)
                  (return 4)))
          (or (return 2)
              (or (return 5)
                  (return 6)))

tree' :: Prog '[Stop, Or, Once] Int
tree' = tree

foo :: String
foo = show tree'

prop_list :: Property
prop_list = property $
  sort (list tree) === [1 .. 6]

genNondet :: (Members '[Or, Stop] sig, MonadGen m) => m (Prog sig Int)
genNondet = Gen.recursive Gen.choice
  [ pure stop ]
  [ or <$> genNondet <*> genNondet]

prop_list' :: Property
prop_list' = property $ do
  tree <- forAll genNondet
  lift $ putStrLn (show tree)
  sort (list tree) === reverse (list tree)

-- deriving instance (Show a, Show (Effs [Or, Once])
--   => Show (Effs '[Stop, Or, Once] (Prog '[Stop, Or, Once]) (Prog '[Stop, Or, Once] a))

-- instance Show a => Show (Effs '[Stop, Or, Once] (Prog '[Stop, Or, Once]) (Prog '[Stop, Or, Once] a)) where
--   show (Eff (Alg (Stop)))                  = show (Alg Stop)
--   show (Effs (Eff (Alg (Or x y))))         = show @(Eff Or   (Prog [Stop, Or, Once]) (Prog [Stop, Or, Once] a)) (Alg (Or x y))
--   show (Effs (Effs (Eff (Scp (Once p)))))  = show @(Eff Once (Prog [Stop, Or, Once]) (Prog [Stop, Or, Once] a)) (Scp (Once p))

deriving instance Show (Effs '[] f a)

-- instance
--   ( Show (Eff sig (Prog (sig : sigs)) (Prog (sig : sigs) a))
--   , Show (Effs sigs (Prog (sig ': sigs)) (Prog (sig ': sigs) a))) =>
--   Show (Effs (sig ': sigs) (Prog (sig ': sigs)) (Prog (sig ': sigs) a)) where
--   show (Eff x)  = show x
--   show (Effs x) = show x

-- instance
--   ( Show (sig (Prog f a)), Show (sig (Prog f (Prog f a)))
--   , Show (Effs sigs (Prog f) (Prog f a))) =>
--   Show (Effs (sig ': sigs) (Prog f) (Prog f a)) where
--   show (Eff x)  = show x
--   show (Effs x) = show x

deriving instance
  ( forall x . Show x => Show (sig x)
  , forall x g . (Show x, Show (g x)) => Show (Effs sigs g x)
  , forall x . Show x => Show (f x)
  , Show a) =>
  Show (Effs (sig ': sigs) f a)
  -- show (Effs (Eff (Alg (Or x y))))         = show @(Eff Or   (Prog [Stop, Or, Once]) (Prog [Stop, Or, Once] a)) (Alg (Or x y))
  -- show (Effs (Effs (Eff (Scp (Once p)))))  = show @(Eff Once (Prog [Stop, Or, Once]) (Prog [Stop, Or, Once] a)) (Scp (Once p))

-- deriving instance
--   ( Show (Eff sig (Prog (sig ': sigs)) (Prog (sig ': sigs) a))
--   , Show (Effs sigs (Prog (sig ': sigs)) (Prog (sig ': sigs) a))) =>
--   Show (Effs (sig ': sigs) (Prog (sig ': sigs)) (Prog (sig ': sigs) a))
-- 
-- instance Show (Effs [Or, Once] (Prog [Stop, Or, Once]) (Prog [Stop, Or, Once] Int)) where
--   show (Eff x) = _

-- instance (Show (Eff sig' (Prog (sig : sig' : sigs)) (Prog (sig : sig' : sigs) a)))
--   => Show (Effs (sig' ': sigs) (Prog (sig ': (sig' ': sigs))) (Prog (sig ': (sig' ': sigs)) a)) where
--   show (Eff x) = _

props :: Group
props = $$(discover)
