module Hangman

import Data.Vect
import Vector
                
data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
     MkWordState : (word : String) -> (missing : Vect letters Char) -> WordState guesses_remaining letters

data Finished : Type where
     Lost : (game : WordState 0 (S letters)) -> Finished
     Won  : (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
     Letter : (c : Char) -> ValidInput [c]


total
emptyString : ValidInput [] -> Void
emptyString (Letter _) impossible

total
moreThanOne : ValidInput (x :: (y :: xs)) -> Void
moreThanOne (Letter _) impossible

total
isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No emptyString
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No moreThanOne


total
isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)
     
readGuess : IO (x ** ValidInput x)                       
readGuess = do putStr "Guess:"
               x <- getLine
               case isValidString (toUpper x) of
                    (Yes prf) => pure (_ ** prf)
                    (No contra) => do putStrLn "Invalid guess"
                                      readGuess

processGuess : (letter : Char) ->
               WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess letter (MkWordState word missing)
  = case isElem letter missing of
         (Yes prf) => Right (MkWordState word (removeElem_auto letter missing))
         (No contra) => Left (MkWordState word missing)

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st 
               = do (_ ** Letter letter) <- readGuess
                    case processGuess letter st of
                         (Left l) => do putStrLn "Wrong!"
                                        case guesses of
                                             Z => pure (Lost l)
                                             (S k) => game l
                         (Right r) => do putStrLn "Right!"
                                         case letters of
                                             Z => pure (Won r)
                                             S k => game r

main : IO ()
main = do result <- game {guesses=2} 
                         (MkWordState "Test" ['T', 'E', 'S'])
          case result of
               (Lost (MkWordState word missing)) => 
                     putStrLn ("You lose. The word was " ++ word)
               (Won (MkWordState word missing)) => 
                    putS trLn "You win!"
