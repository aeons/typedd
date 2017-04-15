data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs,ys,zs,ws

sameCons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
sameCons {xs = []} {ys = []} prf = Refl
sameCons prf = cong prf

sameLists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
sameLists {xs = []} {ys = []} Refl prf = Refl
sameLists Refl prf = sameCons prf

data ThreeEq : a -> b -> c -> Type where
  Three : ThreeEq x x x

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS k k k Three = Three

plusCommutes' : (n : Nat) -> (m : Nat) -> n + m = m + n
plusCommutes' Z m = rewrite plusZeroRightNeutral m in Refl
plusCommutes' (S k) m
  = rewrite plusSuccRightSucc k m in
    rewrite sym (plusSuccRightSucc m k) in
            plusCommutes' k (S m)

reverse' : Vect n a -> Vect n a
reverse' xs = reverse'' [] xs
  where
    reverseProofNil : Vect n a -> Vect (plus n 0) a
    reverseProofNil {n} xs = rewrite plusZeroRightNeutral n in xs

    reverseProofXs : Vect ((S n) + m) a -> Vect (plus n (S m)) a
    reverseProofXs {n} {m} = rewrite plusSuccRightSucc n m in id

    reverse'' : Vect n a -> Vect m a -> Vect (n + m) a
    reverse'' acc [] = reverseProofNil acc
    reverse'' acc (x :: xs) = reverseProofXs (reverse'' (x :: acc) xs)

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal {x = x} {y = x} {xs = ys} {ys = ys} contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal {x = x} {y = x} {xs = ys} {ys = ys} contra Refl = contra Refl

DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys)
    = case decEq x y of
           No contra => No (headUnequal contra)
           Yes Refl  => case decEq xs ys of
                             No contra => No (tailUnequal contra)
                             Yes prf => Yes (cong prf)
