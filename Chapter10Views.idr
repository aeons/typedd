import Data.List.Views
import Data.Nat.Views
import Data.Vect
import Data.Vect.Views

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys = reverse (helper xs ys) where
  helper xs ys with (snocList xs)
    helper [] ys | Empty = []
    helper (xs ++ [x]) ys | (Snoc recXs) with (snocList ys)
      helper (xs ++ [x]) [] | (Snoc recXs) | Empty = []
      helper (xs ++ [x]) (ys ++ [y]) | (Snoc recXs) | (Snoc recYs)
        = if x == y
          then x :: (helper xs ys | recXs | recYs)
          else []

mergeSort : Ord a => Vect n a -> Vect n a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (xs ++ ys) | (SplitRecPair lrec rrec)
    = let left = mergeSort xs | lrec
          right = mergeSort ys | rrec in
          merge left right

toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1"

palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (xs ++ [y])) | (VCons rec)
    = if x == y
      then palindrome xs | rec
      else False
