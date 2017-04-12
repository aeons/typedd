module Main

import Data.Vect

data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newitem = MkData _ (items ++ [newitem])

data Command = Add String
             | Get Integer
             | Size
             | Search String
             | Quit

stringToInteger : String -> Maybe Integer
stringToInteger maybeInt
  = case all isDigit (unpack maybeInt) of
    False => Nothing
    True  => Just (cast maybeInt)

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add"    item  = Just (Add item)
parseCommand "get"    id    = map Get $ stringToInteger id
parseCommand "size"   ""    = Just Size
parseCommand "search" query = Just (Search query)
parseCommand "quit"   ""    = Just Quit
parseCommand _        _     = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
  (cmd, args) => parseCommand cmd (ltrim args)

getEntry : Integer -> DataStore -> Maybe (String, DataStore)
getEntry id store
  = let storeItems = items store in
    case integerToFin id (size store) of
      Nothing  => Just ("Index out of range\n", store)
      Just id' => Just (index id' storeItems ++ "\n", store)

find : String -> DataStore -> String
find query store
  = unlines . toList $ snd $ filter (isInfixOf query) (items store)

findWithIndex : String -> DataStore -> String
findWithIndex query (MkData _ items)
  = let indices = findIndices (isInfixOf query) items
        elems = map (\i => index i items) indices in
        unlines $ zipWith format indices elems where
          format : Fin n -> String -> String
          format i s = show (finToInteger i) ++ ": " ++ s


processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
  = case parse input of
    Nothing             => Just ("Command not recognized\n", store)
    Just (Add item)     => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
    Just (Get id)       => getEntry id store
    Just Size           => Just ("Size " ++ show (size store) ++ "\n", store)
    Just (Search query) => Just (findWithIndex query store, store)
    Just Quit           => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
