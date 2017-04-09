module Chapter2

palindrome : Nat -> String -> Bool
palindrome minLen s = let len = length s
                          lc = toLower s in
                          len > minLen && lc == reverse lc

export
counts : String -> (Nat, Nat)
counts x = (length (words x), length x)

topTen : Ord a => List a -> List a
topTen = List.take 10 . reverse . sort

overLength : Nat -> List String -> Nat
overLength k = length . filter (> k) . map length
