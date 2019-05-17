module Interactive

import System
import Data.Vect

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input) then pure (Just (cast input)) else pure Nothing

export
readNumbers : IO (Maybe (Nat, Nat))
readNumbers =
  do Just n1 <- readNumber | Nothing => pure Nothing
     Just n2 <- readNumber | Nothing => pure Nothing
     pure (Just (n1, n2))

countdown : (secs : Nat) -> IO ()
countdown Z = putStrLn "Lift off!"
countdown (S secs) = do putStrLn (show (S secs))
                        usleep 1000000
                        countdown secs
                        
countdowns : IO ()                        
countdowns = do putStr "Enter starting number: "
                Just startNum <- readNumber 
              | Nothing => do putStrLn "Invalid input"
                              countdowns
                countdown startNum
                putStr "Another (y/n)? "
                yn <- getLine
                if yn == "y" then countdowns
                             else pure ()

export
guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = do putStrLn ("Guess " ++ (show guesses))
                          putStr "Make a guess: "
                          Just number <- readNumber | Nothing => do putStrLn "Invalid input"
                                                                    guess target guesses
                          case compare number target of
                               LT => do putStrLn "To low"
                                        guess target (guesses + 1)
                               EQ => pure ()
                               GT => do putStrLn "To high"
                                        guess target (guesses + 1)


repl' : String -> (String -> String) -> IO ()
repl' prompt fn = do putStr prompt
                     input <- getLine
                     putStrLn (fn input)
                     repl' prompt fn
                     
replWith' : a -> String -> (a -> String -> Maybe (String, a)) -> IO ()                     
replWith' state prompt fn = do putStr prompt
                               input <- getLine
                               case fn state input of
                                 Nothing => replWith' state prompt fn
                                 Just (output, state') => do putStrLn output
                                                             replWith' state' prompt    fn
readVectLen : (len : Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) = do x <- getLine
                       xs <- readVectLen k
                       pure (x :: xs)
                       
data VectUnknown : Type -> Type where
     MkVect : (len : Nat) -> Vect len a -> VectUnknown a


readVect : IO (VectUnknown String)
readVect = do x <- getLine
              if (x == "")
                 then pure (MkVect _ [])
                 else do MkVect _ xs <- readVect
                         pure (MkVect _ (x :: xs))

printVect : Show a => VectUnknown a -> IO ()
printVect (MkVect len xs) = putStrLn (show xs ++ " (length " ++ show len ++ ") ")

readVect' : IO (len ** Vect len String)
readVect' = do x <- getLine
               if (x == "")
               then pure (_ ** [])
               else do (_ ** xs) <- readVect'
                       pure (_ ** x :: xs)

zipInputs : IO ()
zipInputs = do putStrLn "Enter first vector (blank line to end):"
               (len1 ** v1) <- readVect'
               putStrLn "Enter second vector (blank line to end):"
               (len2 ** v2) <- readVect'
               case exactLength len2 v1 of
                    Nothing => putStrLn "Different lengths!"
                    Just v1' => printLn (zip v1' v2)
               
 
-- Exercises

readToBlank : IO (List String)
readToBlank = do x <- getLine
                 if x == "" 
                 then pure []
                 else do xs <- readToBlank
                         pure (x :: xs)
                         

readAndSave : IO ()
readAndSave = do putStrLn "Enter text, blank line to end:"
                 xs <- readToBlank
                 putStrLn "Enter filename:"
                 x <- getLine
                 if x == ""
                 then putStrLn "Empty file name not allowed..."
                 else do result <- writeFile x (show xs) 
                         case result of
                              (Left l) => putStrLn "Error writing to file"
                              (Right r) => putStrLn "Not error writing to file"
                              
readToEOF : File -> IO (n ** Vect n String)
readToEOF h = do end <- fEOF h
                 if end 
                 then pure (0 ** [])
                 else do Right x <- fGetLine h | Left _ => pure (0 ** [])
                         (_ ** xs) <- readToEOF h
                         pure (_ ** x :: xs)
                         
                              
                              
export
readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do Right h <- openFile filename Read 
                           | Left err => pure (_ ** [])
                           lines <- readToEOF h
                           pure lines

