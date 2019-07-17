module Hangman

import Data.Vect
                
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

game : WordState (S guesses) (S letters) -> IO Finished
game st = ?game_rhs
