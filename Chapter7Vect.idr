module Vect

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

Eq ty => Eq (Vect n ty) where
  (==) [] [] = True
  (==) (x :: xs) (y :: ys) = x == y && xs == ys

Foldable (Vect n) where
  foldr f acc [] = acc
  foldr f acc (x :: xs) = f x (foldr f acc xs)
