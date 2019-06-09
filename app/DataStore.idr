module DataStore

import Data.Vect

-- A parameter is unchanged across the entire structure (every element of the vector has the same type)
-- An index may change across a structure (every subvector has a different length)

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
       constructor MkData
       schema : Schema
       size : Nat
       items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newItem = MkData _ _ (addToData items)
  where
    addToData : Vect old (SchemaType schema) -> Vect (S old) (SchemaType schema)
    addToData [] = [newItem]
    addToData (item :: items') = item :: addToData items'
    
display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (iteml, itemr) = display iteml ++ ", " ++ display itemr

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = let storeItems = items store in
                               case integerToFin pos (size store) of
                                    Nothing => Just ("Out of range\n", store)
                                    Just id => Just (display (index id storeItems) ++ "\n", store)
    
                  
data Command : Schema -> Type where
             Add : SchemaType schema -> Command schema
             Get : Integer -> Command schema
--             Search : String -> Command schema
             Size : Command schema
             Quit : Command schema
             
parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)             
parsePrefix SString item = Just (item, "")
parsePrefix SInt input = case span isDigit input of
                              ("", rest) => Nothing
                              (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schemal .+. schemar) item = case parsePrefix schemal item of
                                              Nothing => Nothing
                                              Just (schema, rest) => case parsePrefix schemar rest of
                                                                         Nothing => Nothing
                                                                         Just (schema', "") => Just ((schema, schema'), "")
                                                                         Just (schema', rest) => Nothing

parseBySchema : (schema : Schema) -> (str : String) -> Maybe (SchemaType schema)
parseBySchema schema str = case parsePrefix schema str of
                                Just (res, "") => Just res
                                Just _ => Nothing
                                Nothing => Nothing

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "add" str = case parseBySchema schema str of
                                     Nothing => Nothing
                                     (Just item) => Just (Add item)
parseCommand schema "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
-- parseCommand schema "search" str = Just (Search str)                              
parseCommand schema "size" "" = Just Size
parseCommand schema "quit" "" = Just Quit
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case Strings.span (/= ' ') input of
                   (cmd, args) => parseCommand schema cmd (ltrim args)
                   
-- search : (store : DataStore) -> String -> (SchemaType (schema store))
-- search store str = toString (searchItems 0 (items store) str)
--                  where
--                    searchItems : Int -> Vect n String -> String -> List (Int, String)
--                    searchItems pos [] str = []
--                    searchItems pos (x :: xs) str = case Strings.isInfixOf str x of
--                                                        False => searchItems (pos + 1) xs str
--                                                        True => (pos, x) :: searchItems (pos + 1) xs str
--                    toString : List (Int, String) -> String
--                    toString [] = ""
--                    toString ((pos, item) :: xs) = show pos ++ ": " ++ item ++ "\n" ++ toString xs


processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse (schema store) input of
                                Nothing => Just ("Invalid command\n", store)
                                Just (Add item) => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                                Just (Get pos) => getEntry pos store
--                                Just (Search x) => Just (search store str, store)
                                Just Size => Just ("There are " ++ show (size store) ++ " items in store\n", store)
                                Just Quit => Nothing
