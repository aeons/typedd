module Main

import System

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
    then pure $ Just $ cast input
    else pure Nothing

-- failedGuess : String -> Nat -> IO () -> IO ()
-- failedGuess msg f = do putStrLn msg
                      --  f

guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = do
    Just guessed <- readNumber
      | Nothing => do putStrLn "Invalid input"
                      guess target guesses
    case compare guessed target of
      LT => failedGuess "Guess too low"
      EQ => putStrLn $ "Number guessed in " ++ show guesses ++ " guesses!"
      GT => failedGuess "Guess too high"
  where
    failedGuess : String -> IO ()
    failedGuess msg = do putStrLn $ msg ++ " (" ++ show guesses ++ " guesses)"
                         guess target (S guesses)

repl' : String -> (String -> String) -> IO ()
repl' prompt f = do
  putStr prompt
  input <- getLine
  putStr (f input)
  repl' prompt f

replWith' : a -> String -> (a -> String -> Maybe (String, a)) -> IO ()
replWith' initial prompt f = do
  putStr prompt
  input <- getLine
  case f initial input of
    Nothing => pure ()
    Just (output, state) => do putStr output
                               replWith' state prompt f

main : IO ()
main = do
  random <- time
  let target = the Nat $ cast $ mod random 101
  putStrLn "Guess a number!"
  guess target 1
