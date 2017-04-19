import Data.Primitives.Views

labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith _ [] = []
labelWith (label :: labels) (value :: values) = (label, value) :: labelWith labels values

label : List a -> List (Integer, a)
label xs = labelWith [0..] xs

everyOther : Stream a -> Stream a
everyOther (_ :: x :: xs) = x :: everyOther xs

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem

%name InfList xs,ys,zs,ws

countFrom : Num a => a -> InfList a
countFrom x = x :: countFrom (x + 1)

getPrefix : Nat -> InfList a -> List a
getPrefix Z _ = []
getPrefix (S k) (x :: xs) = x :: getPrefix k xs

Functor InfList where
  map f (x :: xs) = f x :: map f xs

data Face = Heads | Tails

getFace : Int -> Face
getFace x with (divides x 2)
  getFace ((2 * div) + 0) | (DivBy prf) = Heads
  getFace ((2 * div) + rem) | (DivBy prf) = Tails

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips count xs = map getFace $ take count xs

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'


sqrtApprox : (number : Double) -> (approx : Double) -> Stream Double
sqrtApprox number approx = let next = (approx + (number / approx)) / 2 in
                           next :: sqrtApprox number next

sqrtBound : (max : Nat) -> (number : Double) -> (bound : Double) -> (approxs : Stream Double) -> Double
sqrtBound Z number bound (value :: xs) = value
sqrtBound (S k) number bound (approx :: approxs) = let delta = approx * approx - abs number in
                                                       if delta < bound
                                                       then approx
                                                       else sqrtBound k number bound approxs

sqrt : (number : Double) -> Double
sqrt number = sqrtBound 100 number 0.000000000000001 (sqrtApprox number number)
