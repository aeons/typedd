module Chapter5IO

import Data.Vect

readToBlank : IO (List String)
readToBlank = readToBlank' []
  where
    readToBlank' : List String -> IO (List String)
    readToBlank' xs = do ln <- getLine
                         if ln == ""
                         then pure $ reverse xs
                         else readToBlank' (ln :: xs)

readAndSave : IO ()
readAndSave = do
  putStrLn "Enter the contents of the file, end with a blank line"
  lines <- readToBlank
  putStrLn "Enter the filename to save to"
  filename <- getLine
  -- This returns Left FileWriteError on Windows, despite succeeding
  _ <- writeFile filename (unlines lines)
  putStrLn "Successfully wrote to file"

readVect : IO (len ** Vect len String)
readVect = do
  x <- getLine
  if (x == "")
  then pure (_ ** [])
  else do (_ ** xs) <- readVect
          pure (_ ** x :: xs)

fReadVect : File -> IO (n ** Vect n String)
fReadVect f = do
  eof <- fEOF f
  if eof
    then pure (_ ** [])
    else do Right x <- fGetLine f | Left err => pure (_ ** [])
            if trim x == ""
              then pure (_ ** [])
              else do (_ ** xs) <- fReadVect f
                      pure (_ ** trim x :: xs)

readVectFileError : FileError -> IO (n ** Vect n String)
readVectFileError err = do
  putStrLn $ "Error: " ++ show err
  pure (_ ** [])

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right file <- openFile filename Read | Left err => readVectFileError err
  vect <- fReadVect file
  closeFile file
  pure vect
