import System

%default total

data Command : Type -> Type where
  PutStr : String -> Command ()
  PutStrLn : String -> Command ()
  GetLine : Command String
  ReadFile : String -> Command (Either FileError String)
  WriteFile : String -> String -> Command (Either FileError ())
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

runCommand : Command a -> IO a
runCommand (PutStr str) = putStr str
runCommand (PutStrLn str) = putStrLn str
runCommand GetLine = getLine
runCommand (ReadFile filename) = readFile filename
runCommand (WriteFile filename contents) = writeFile filename contents
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

data ShellCommand = Cat String
                   | Copy String String
                   | Unrecognized String
                   | Exit

readShellCommand : Command ShellCommand
readShellCommand = do PutStr "> "
                      cmd <- GetLine
                      case words cmd of
                        ["cat", filename] => Pure (Cat filename)
                        ["copy", from, to] => Pure (Copy from to)
                        ["exit"] => Pure Exit
                        ws => Pure (Unrecognized (unwords ws))

mutual
  error : String -> ConsoleIO ()
  error msg = do PutStrLn msg
                 shell

  cat : String -> ConsoleIO ()
  cat filename = do Right contents <- ReadFile filename
                      | Left err => error "Failed reading file"
                    PutStrLn contents
                    shell

  copy : String -> String -> ConsoleIO ()
  copy src dest = do Right contents <- ReadFile src
                      | Left err => error "Failed reading source file"
                     Right () <- WriteFile dest contents
                      | Left err => error "Failed writing destination file"
                     PutStrLn $ "Copied file from " ++ src ++ " to " ++ dest
                     shell

  shell : ConsoleIO ()
  shell = do cmd <- readShellCommand
             case cmd of
               (Cat filename) => cat filename
               (Copy src dest) => copy src dest
               (Unrecognized cmd) => error $ "Command not recognized: " ++ cmd
               Exit => Quit ()

main : IO ()
main = run shell
