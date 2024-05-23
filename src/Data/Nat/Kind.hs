{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Nat.Kind where
import Data.Nat
import Data.Kind ( Type )

type family Iterate (n :: Nat) (f :: Type -> Type) (a :: Type) :: Type where
  Iterate Z     f a = a
  Iterate (S n) f a = f (Iterate n f a)