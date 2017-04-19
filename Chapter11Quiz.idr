import Data.Primitives.Views
import System

%default total

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

runCommand : Command a -> IO a
runCommand (PutStr str) = putStr str
runCommand GetLine = getLine
runCommand (Pure val) = pure val
runCommand (Bind c f) = do res <- runCommand c
                           runCommand (f res)

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

run : ConsoleIO a -> IO a
run (Quit val) = pure val
run (Do c f) = do res <- runCommand c
                  run (f res)

data Input = Answer Int | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      input <- GetLine
                      if toLower input == "quit"
                        then Pure QuitCmd
                        else Pure (Answer (cast input))

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

quizInputs : IO (Stream Int)
quizInputs = do seed <- time
                pure $ arithInputs (fromInteger seed)


mutual
  correct : Stream Int -> (score : Nat) -> (questions : Nat) -> ConsoleIO ()
  correct ns score questions
    = do PutStr "Correct!"
         quiz ns (score + 1) (questions + 1)

  wrong : Stream Int -> (answer : Int) -> (score : Nat) -> (questions : Nat) -> ConsoleIO ()
  wrong ns answer score questions
    = do PutStr $ "Wrong, the answer is " ++ show answer ++ "\n"
         quiz ns score (questions + 1)

  quiz : Stream Int -> (score : Nat) -> (questions : Nat) -> ConsoleIO ()
  quiz (n1 :: n2 :: ns) score questions
    = do PutStr $ "Score so far: " ++ show score ++ " / " ++ show questions ++ "\n"
         input <- readInput $ show n1 ++ " * " ++ show n2 ++ "? "
         case input of
           (Answer answer) => if answer == n1 * n2
                                then correct ns score questions
                                else wrong ns (n1 * n2) score questions
           QuitCmd => do PutStr $ "Final score: " ++ show score ++ " / " ++ show questions ++ "\n"
                         Quit ()


main : IO ()
main = do randoms <- quizInputs
          run $ quiz randoms 0 0
