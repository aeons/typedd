module Chapter3

import Data.Vect

llength : List a -> Nat
llength [] = 0
llength (x :: xs) = 1 + llength xs

lreverse : List a -> List a
lreverse [] = []
lreverse (x :: xs) = (lreverse xs) ++ [x]

lmap : (a -> b) -> List a -> List b
lmap f [] = []
lmap f (x :: xs) = f x :: lmap f xs

vmap : (a -> b) -> Vect n a -> Vect n b
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs
