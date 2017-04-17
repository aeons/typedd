module Hangman

import Data.Vect

%default total

data WordState : (guessesRemaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word : String) ->
                (missing : Vect letters Char) ->
                WordState guessesRemaining letters

data Finished : Type where
  Lost : (game : WordState 0 (S letters)) -> Finished
  Won  : (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
  Letter : (c : Char)  -> ValidInput [c]

Uninhabited (ValidInput []) where
  uninhabited prf impossible

Uninhabited (ValidInput (x :: y :: xs)) where
  uninhabited prf impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No absurd
isValidInput [c] = Yes (Letter c)
isValidInput (x :: y :: xs) = No absurd

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

partial
readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess: "
               x <- getLine
               case isValidString x of
                 Yes prf => pure (_ ** prf)
                 No contra => do putStrLn "Invalid guess"
                                 readGuess

removeElem : (value : a) -> (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem value (value :: xs) {prf = Here} = xs
removeElem {n = Z} value (x :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (x :: xs) {prf = There later} = x :: removeElem value xs

processGuess : (letter : Char) ->
               WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess letter (MkWordState word missing)
  = case isElem letter missing of
         Yes prf   => Right (MkWordState word (removeElem letter missing))
         No contra => Left  (MkWordState word missing)


partial
game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} state
  = do ([guess] ** _) <- readGuess
       case processGuess guess state of
            Left l => do putStrLn "Wrong!"
                         case guesses of
                              Z => pure (Lost l)
                              S k => game l
            Right r => do putStrLn "Right!"
                          case letters of
                               Z => pure (Won r)
                               S k => game r



partial
main : IO ()
main = do result <- game {guesses=2} (MkWordState "Test" ['T', 'E', 'S'])
          case result of
            Lost (MkWordState word missing) =>
              putStrLn ("You lose. The word was " ++ word)
            Won (MkWordState word missing) =>
              putStrLn ("You win. The word was " ++ word)
