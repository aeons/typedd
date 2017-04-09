module Main

import Chapter2

showCounts : String -> String
showCounts x = show (counts x) ++ "\n"

main : IO ()
main = repl "Enter a sentence: " showCounts
