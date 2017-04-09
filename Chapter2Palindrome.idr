module Main

palindrome : String -> Bool
palindrome x = let lc = toLower x in
                    lc == reverse lc

showPalindrome : String -> String
showPalindrome x = show (palindrome x) ++ "\n"

main : IO ()
main = repl "Enter a string: " showPalindrome
