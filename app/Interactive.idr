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
