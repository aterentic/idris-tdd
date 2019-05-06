module DataStore

import Data.Vect

-- A parameter is unchanged across the entire structure (every element of the vector has the same type)
-- An index may change across a structure (every subvector has a different length)

public export
data DataStore : Type where
     MkData : (size : Nat) ->
              (items : Vect size String) ->
              DataStore
              
size : DataStore -> Nat              
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newItem = MkData _ (addToData items)
  where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [newItem]
    addToData (item :: items') = item :: addToData items'
       
data Command = Add String
             | Get Integer
             | Search String
             | Size
             | Quit

parseCommand : String -> String -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand "search" str = Just (Search str)                              
parseCommand "size" "" = Just Size
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case Strings.span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = let storeItems = items store in
                               case integerToFin pos (size store) of
                                    Nothing => Just ("Out of range\n", store)
                                    Just id => Just (index id storeItems ++ "\n", store)
                                    

search : (store : DataStore) -> String -> String
search store str = toString (searchItems 0 (items store) str)
                 where
                   searchItems : Int -> Vect n String -> String -> List (Int, String)
                   searchItems pos [] str = []
                   searchItems pos (x :: xs) str = case Strings.isInfixOf str x of
                                                       False => searchItems (pos + 1) xs str
                                                       True => (pos, x) :: searchItems (pos + 1) xs str
                   toString : List (Int, String) -> String
                   toString [] = ""
                   toString ((pos, item) :: xs) = show pos ++ ": " ++ item ++ "\n" ++ toString xs



processCommand : (cmd : Command) -> (store : DataStore) -> Maybe (String, DataStore)
processCommand (Add item) store = Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
processCommand (Get pos) store = getEntry pos store
processCommand (Search str) store = Just (search store str, store)
processCommand Size store = Just ("There are " ++ show (size store) ++ " items in store\n", store)
processCommand Quit store = Nothing


export
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse input of
                                Nothing => Just ("Invalid command\n", store)
                                (Just cmd) => processCommand cmd store

