%default total

data Elem : a -> List a -> Type where
  Here : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

Uninhabited (Last [] value) where
  uninhabited LastOne impossible

notLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
notLast contra LastOne = contra Refl
notLast contra (LastCons prf) = absurd prf

notLastInTail : (Last (x :: xs) value -> Void) -> Last (_ :: x :: xs) value -> Void
notLastInTail contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No absurd
isLast [x] value
  = case decEq x value of
         Yes Refl => Yes LastOne
         No contra => No (notLast contra)
isLast (_ :: x :: xs) value
  = case isLast (x :: xs) value of
         Yes prf => Yes (LastCons prf)
         No contra => No (notLastInTail contra)
