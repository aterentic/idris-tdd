import Data.Primitives.Views
import System

record Score where
       constructor MkScore
       correct : Nat
       attempted : Nat

record GameState where
       constructor MkGameState
       score : Score
       difficulty : Int

initState : GameState
initState = MkGameState (MkScore 0 0) 12

Show GameState where
  show st = show (correct (score st)) ++ "/" ++
            show (attempted (score st)) ++ "\n" ++
            "Difficulty: " ++ show (difficulty st)

setDifficulty : Int -> GameState -> GameState
setDifficulty newDiff = record { difficulty = newDiff } 

addWrong : GameState -> GameState
addWrong = record { score->attempted $= (+1) }

addCorrect : GameState -> GameState
addCorrect = record { score->correct $= (+1), score->attempted $= (+1) }

data Command : Type -> Type where
     PutStr : String -> Command ()
     GetLine : Command String
     
     GetRandom : Command Int
     GetGameState : Command GameState
     PutGameState : GameState -> Command ()
     
     Pure : ty -> Command ty
     Bind : Command a -> (a -> Command b) -> Command b

mutual
  Functor Command where
    map f cmd = do val <- cmd
                   pure (f val)

  Applicative Command where
    pure = Pure
    (<*>) f a = do f' <- f
                   a' <- a
                   pure (f' a')
  
  Monad Command where
    (>>=) = Bind

runCommand : Stream Int -> GameState -> Command a -> IO (a, Stream Int, GameState)
runCommand rnds state (PutStr x) = do putStr x 
                                      pure ((), rnds, state)
runCommand rnds state GetLine = do str <- getLine
                                   pure (str, rnds, state)
runCommand (val :: rnds) state GetRandom 
       = pure (getRandom val (difficulty state), rnds, state)
  where
    getRandom : Int -> Int -> Int
    getRandom val max with (divides val max)
      getRandom val 0 | DivByZero = 1
      getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1
      
runCommand rnds state GetGameState = pure (state, rnds, state)
runCommand rnds state (PutGameState newState) = pure ((), rnds, newState)
runCommand rnds state (Pure val) = pure (val, rnds, state)
runCommand rnds state (Bind c f) = do (res, newRnds, newState) <- runCommand rnds state c
                                      runCommand newRnds newState (f res)

data ConsoleIO : Type -> Type where
     Quit : a -> ConsoleIO a
     Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

data Input = Answer Int
           | QuitCmd
 
readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                         then Pure QuitCmd
                         else Pure (Answer (cast answer))

data Fuel = Dry | More (Lazy Fuel)


run : Fuel -> Stream Int -> GameState -> ConsoleIO a -> IO (Maybe a, Stream Int, GameState)
run fuel rnds state (Quit val) = do pure (Just val, rnds, state)
run (More fuel) rnds state (Do command cont) 
    = do (res, newRnds, newState) <- runCommand rnds state command
         run fuel newRnds newState (cont res)
run Dry rnds state p = pure (Nothing, rnds, state)

showScore : (score : Nat) -> (totalQuestions : Nat) -> String
showScore score totalQuestions =  "Score so far: " ++ show score ++ " / " ++ show totalQuestions ++ "\n"

mutual
  correct : ConsoleIO GameState
  correct = do PutStr "Correct!\n"
               st <- GetGameState
               PutGameState (addCorrect st)
               quiz
 
  wrong : Int -> ConsoleIO GameState
  wrong ans = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
                 st <- GetGameState
                 PutGameState (addWrong st)
                 quiz
  
  quiz : ConsoleIO GameState
  quiz = do num1 <- GetRandom
            num2 <- GetRandom
            st <- GetGameState
            PutStr (show st ++ "\n")
            
            input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
            case input of
                 Answer answer => if answer == num1 * num2
                                     then correct
                                     else wrong (num1 * num2)
                 QuitCmd => Quit st

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 101394223 in
                   (seed' `shiftR` 2) :: randoms seed'

forever : Fuel
forever = More forever

partial
main : IO ()
main = do seed <- time
          (Just score, _, state) <-
                run forever (randoms (fromInteger seed)) initState quiz
                    | _ => putStrLn "Ran out of fuel"
          putStrLn ("Final score: " ++ show state)

updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = do state <- GetGameState
                       PutGameState (f state)

correct' : ConsoleIO GameState
correct' = do PutStr "Correct!\n"
              updateGameState addCorrect
              quiz

record Votes where
       constructor MkVotes
       upvotes : Integer
       downvotes : Integer

record Article where
       constructor MkArticle
       title : String
       url : String
       score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

getScore : Article -> Integer
getScore (MkArticle title url (MkVotes upvotes downvotes)) = upvotes - downvotes

badSite : Article
badSite = MkArticle "Bad Page" "http://example.com/bad" (MkVotes 5 47)

goodSite : Article
goodSite = MkArticle "Good Page" "http://example.com/good" (MkVotes 101 7)

addUpvote : Article -> Article
addUpvote state = record { score->upvotes $= (+1) } state

addDownvote : Article -> Article
addDownvote state = record { score->downvotes $= (+1) } state
