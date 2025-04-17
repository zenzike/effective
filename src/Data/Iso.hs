module Data.Iso where

data Iso a b = Iso { fwd :: !(a -> b), bwd :: !(b -> a) }

refl :: Iso a a
refl = Iso id id

sym :: Iso a b -> Iso b a
sym (Iso f g) = Iso g f

trans :: Iso a b -> Iso b c -> Iso a c
trans (Iso f g) (Iso h k) = Iso (h . f) (g . k)