module Chapter3Matrix

import Data.Vect

Matrix : Nat -> Nat -> Type -> Type
Matrix n m elem = Vect n (Vect m elem)

%name Matrix xs,ys,zs,ws

transposeMat : Matrix n m elem -> Matrix m n elem
transposeMat []        = replicate _ []
transposeMat (x :: xs) = zipWith (::) x (transpose xs)

matrixAdd : Num elem => Matrix n m elem -> Matrix n m elem -> Matrix n m elem
matrixAdd [] [] = []
matrixAdd (x :: xs) (y :: ys) = zipWith (+) x y :: matrixAdd xs ys

vectVectMult : Num elem => Vect n elem -> Vect n elem -> Vect n elem
vectVectMult = zipWith (*)

matrixVectMult : Num elem => Matrix n m elem -> Vect m elem -> Vect n elem
matrixVectMult [] _               = []
matrixVectMult (row :: rest) vect = let rowSum = sum $ zipWith (*) row vect in
                                    rowSum :: matrixVectMult rest vect

matrixMult : Num elem => Matrix n m elem -> Matrix m p elem -> Matrix n p elem
matrixMult xs ys = transpose $ map (matrixVectMult xs) (transpose ys)
