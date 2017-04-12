module Main

import Data.Vect

%default total

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y  )

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) item
  = MkData schema _ (items ++ [item])

data Command : Schema -> Type where
  SetSchema : (newSchema : Schema) -> Command schema
  Add : SchemaType schema -> Command schema
  Get : Integer -> Command schema
  GetAll : Command schema
  Quit : Command schema

stringToInteger : String -> Maybe Integer
stringToInteger maybeInt
  = if all isDigit (unpack maybeInt)
    then Just (cast maybeInt)
    else Nothing

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs)
      = case span (/= '"') xs of
             (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
             _                     => Nothing
    getQuoted _ = Nothing
parsePrefix SInt input
  = case span isDigit input of
         ("", _)     => Nothing
         (num, rest) => Just (cast num, ltrim rest)
parsePrefix SChar input
  = case unpack input of
    char :: ' ' :: rest => Just (char, ltrim (pack rest))
    _                   => Nothing
parsePrefix (schemal .+. schemar) input
  = do (left, input') <- parsePrefix schemal input
       (right, input'') <- parsePrefix schemar input'
       pure ((left, right), input'')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
                                  Just (res, "") => Just res
                                  _              => Nothing

mutual
  parseSchema : List String -> Maybe Schema
  parseSchema ("String" :: xs) = parseSchema' SString xs
  parseSchema ("Int"    :: xs) = parseSchema' SInt xs
  parseSchema ("Char"   :: xs) = parseSchema' SChar xs
  parseSchema _                = Nothing

  parseSchema' : Schema -> List String -> Maybe Schema
  parseSchema' schema [] = Just schema
  parseSchema' schema xs = map ((.+.) schema) (parseSchema xs)

parseCommand : (schema : Schema) ->
               (cmd : String) ->
               (args : String) ->
               Maybe (Command schema)
parseCommand schema "schema" input = map SetSchema (parseSchema (words input))
parseCommand schema "add"    item  = map Add (parseBySchema schema item)
parseCommand schema "get"    ""    = Just GetAll
parseCommand schema "get"    id    = map Get (stringToInteger id)
parseCommand schema "quit"   ""    = Just Quit
parseCommand _      _        _     = Nothing

parse : (schema : Schema) ->
        (input : String) ->
        Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item    = show item
display {schema = SChar} item   = show item
display {schema = (x .+. y)} (iteml, itemr)
  = display iteml ++ ", " ++ display itemr

getEntry : Integer -> (store : DataStore) -> Maybe (String, DataStore)
getEntry id store
  = case integerToFin id (size store) of
      Nothing  => Just ("Index out of range\n", store)
      Just id' => Just (display (index id' (items store)) ++ "\n", store)

getEntries : DataStore -> Maybe (String, DataStore)
getEntries store = Just (showItems 0 (items store), store)
  where
    showItems : Nat -> Vect _ (SchemaType (schema store)) -> String
    showItems _ []        = ""
    showItems n (x :: xs) = show n ++ ": " ++ display x ++ "\n" ++ showItems (S n) xs

setSchema : DataStore -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just (MkData schema _ [])
                              _ => Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
  = case parse (schema store) input of
         Nothing                  => Just ("Command not recognized\n", store)
         Just (SetSchema schema') =>
           case setSchema store schema' of
             Nothing => Just ("Can't update schema on non-empty store\n", store)
             Just store' => Just ("OK\n", store')
         Just (Add item)          =>
           Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
         Just (Get id)            => getEntry id store
         Just GetAll              => getEntries store
         Just Quit                => Nothing

partial
main : IO ()
main = replWith (MkData (SString .+. SString) _ [])
                "Command: " processInput
