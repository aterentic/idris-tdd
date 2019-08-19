module Hangman

import Data.Vect
import Vector

%default total

data GameState : Type where
     NotRunning : GameState
     Running : (guesses : Nat) -> (letters : Nat) -> GameState
                
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

partial
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

partial
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

-- partial
-- main : IO ()
-- main = do result <- game {guesses=2} 
--                          (MkWordState "Test" ['T', 'E', 'S'])
--           case result of
--                (Lost (MkWordState word missing)) => 
--                      putStrLn ("You lose. The word was " ++ word)
--                (Won (MkWordState word missing)) => 
--                     putStrLn "You win!"

letters : String -> List Char
letters str = nub (map toUpper (unpack str))

data GuessResult = Correct | Incorrect

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
     NewGame : (word : String) ->
               GameCmd () NotRunning
                          (const (Running 6 (length $ letters word)))
     Won' : GameCmd () (Running (S guesses) 0)
                      (const NotRunning)
     Lost' : GameCmd () (Running 0 (S letters))
                       (const NotRunning)
     
     Guess : (c : Char) ->
             GameCmd GuessResult 
                     (Running (S guesses) (S letters))
                     (\res => case res of 
                                   Correct => Running (S guesses) letters
                                   Incorrect => Running guesses (S letters))
     
     Pure : (res : ty) -> GameCmd ty (state_fn res) state_fn
     (>>=) : GameCmd a state1 state2_fn ->
             ((res : a) -> GameCmd b (state2_fn res) state3_fn) ->
             GameCmd b state1 state3_fn
     
     ShowState : GameCmd () state (const state)
     Message : String -> GameCmd () state (const state)
     ReadGuess : GameCmd Char state (const state)

namespace Loop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
       (>>=) : GameCmd a state1 state2_fn ->
               ((res : a) -> Inf (GameLoop b (state2_fn res) state3_fn)) ->
               GameLoop b state1 state3_fn
       Exit : GameLoop () NotRunning (const NotRunning)

gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
gameLoop {guesses} {letters} = do
         ShowState
         g <- ReadGuess
         ok <- Guess g
         case ok of
              Correct => case letters of
                              Z => do Won'
                                      ShowState
                                      Exit
                              (S k) => do Message "Correct"
                                          gameLoop
              Incorrect => case guesses of
                                Z => do Lost'
                                        ShowState
                                        Exit
                                S k => do Message "Incorrect"
                                          gameLoop

hangman : GameLoop () NotRunning (const NotRunning)
hangman = do NewGame "testing"
             gameLoop

data Game : GameState -> Type where
     GameStart  : Game NotRunning
     GameWon    : (word : String) -> Game NotRunning
     GameLost   : (word : String) -> Game NotRunning
     InProgress : (word : String) -> 
                  (guesses : Nat) -> 
                  (missing : Vect letters Char) -> 
                  Game (Running guesses letters)

Show (Game g) where
  show GameStart = "Starting"
  show (GameWon word) = "Game won: word was " ++ word
  show (GameLost word) = "Game lost: word was " ++ word
  show (InProgress word guesses missing)
       = "\n" ++ pack (map hideMissing (unpack word))
              ++ "\n" ++ show guesses ++ " guesses left"
    where hideMissing : Char -> Char
          hideMissing c = if c `elem` missing then '-' else c

data Fuel = Dry | More (Lazy Fuel) 

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
     OK : (res : ty) -> Game (outstate_fn res) -> GameResult ty outstate_fn
     OutOfFuel : GameResult ty outstate_fn

ok : (res : ty) -> Game (outstate_fn res) -> IO (GameResult ty outstate_fn)
ok res st = pure (OK res st)

removeElem : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (y :: ys) {prf = There later} = y :: removeElem value ys

runCmd : Fuel ->
         Game instate -> GameCmd ty instate outstate_fn ->
         IO (GameResult ty outstate_fn)
runCmd fuel state (NewGame word) 
       = ok () (InProgress (toUpper word) _ (fromList (letters word)))
runCmd fuel (InProgress word _ missing) Won' = ok () (GameWon word)
runCmd fuel (InProgress word _ missing) Lost' = ok () (GameLost word)
runCmd fuel (InProgress word _ missing) (Guess c) = case isElem c missing of
                                                         (Yes prf) => ok Correct (InProgress word _ (removeElem c missing))
                                                         (No contra) => ok Incorrect (InProgress word _ missing)
runCmd fuel state ShowState = do printLn state
                                 ok () state
runCmd fuel state (Message str) = do putStrLn str
                                     ok () state
runCmd (More fuel) state ReadGuess 
       = do putStr "Guess: "
            input <- getLine
            case unpack input of
                 [x] => if isAlpha x
                           then ok (toUpper x) state
                           else do putStrLn "Invalid input"
                                   runCmd fuel state ReadGuess
                 _ => do putStrLn "Invalid input"
                         runCmd fuel state ReadGuess
runCmd Dry _ ReadGuess = pure OutOfFuel
runCmd fuel state (Pure res) = ok res state
runCmd fuel state (cmd >>= next) 
       = do OK cmdRes newSt <- runCmd fuel state cmd
               | OutOfFuel => pure OutOfFuel
            runCmd fuel newSt (next cmdRes)

run : Fuel ->
      Game instate ->
      GameLoop ty instate outstate_fn ->
      IO (GameResult ty outstate_fn)
run Dry _ _ = pure OutOfFuel
run (More fuel) st (cmd >>= next) 
    = do OK cmdRes newSt <- runCmd fuel st cmd | OutOfFuel => pure OutOfFuel
         run fuel newSt (next cmdRes)
run (More fuel) st Exit = ok () st

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = do run forever GameStart hangman
          pure ()
