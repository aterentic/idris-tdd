import Data.Primitives.Views
import System

%default total

data ShellInput = CatCmd String
                | CopyCmd String String
                | NoCmd
                | ExitCmd

data Input = Answer Int
           | QuitCmd

data Command : Type -> Type where
     ReadFile : String -> Command (Either FileError String)
     WriteFile : String -> String -> Command (Either FileError ())
     PutStr : String -> Command ()
     GetLine : Command String
     
     Pure : ty -> Command ty
     Bind : Command a -> (a -> Command b) -> Command b

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (ReadFile file) = readFile file
runCommand (WriteFile file content) = writeFile file content
runCommand (Pure val) = pure val
runCommand (Bind command cont) = runCommand command >>= \result => runCommand (cont result)

data ConsoleIO : Type -> Type where
     Quit : a -> ConsoleIO a
     Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind
 
readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                         then Pure QuitCmd
                         else Pure (Answer (cast answer))

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run x (Quit val) = pure (Just val)
run (More fuel) (Do c f) = do res <- runCommand c
                              run fuel (f res)
run Dry p = pure Nothing

showScore : (score : Nat) -> (totalQuestions : Nat) -> String
showScore score totalQuestions =  "Score so far: " ++ show score ++ " / " ++ show totalQuestions ++ "\n"

mutual
  correct : Stream Int -> (score : Nat) -> (totalQuestions : Nat) -> ConsoleIO Nat
  correct nums score totalQuestions
          = do PutStr "Correct!\n"
               quiz nums (score + 1) (totalQuestions + 1)

  wrong : Stream Int -> Int -> (score : Nat) -> (totalQuestions : Nat) -> ConsoleIO Nat
  wrong nums ans score totalQuestions
        = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
             quiz nums score (totalQuestions + 1)

  quiz : Stream Int -> (score : Nat) -> (totalQuestions : Nat) -> ConsoleIO Nat
  quiz (n1 :: n2 :: nums) score totalQuestions 
    = do PutStr (showScore score totalQuestions)
         input <- readInput (show n1 ++ " * " ++ show n2 ++ "? ")
         case input of
              (Answer a) => if a == n1 * n2
                            then correct nums score totalQuestions
                            else wrong nums (n1 * n2) score totalQuestions
              QuitCmd => Quit score 

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 101390423 in
                   (seed' `shiftR` 2) :: randoms seed'


arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = do seed <- time
          Just score <- run forever (quiz (arithInputs (fromInteger seed)) 0 0)
               | Nothing => putStrLn "Ran out of fuel"
          putStrLn ("Final score: " ++ show score)

readInput' : (prompt : String) -> Command ShellInput
readInput' prompt = do PutStr prompt
                       cmd <- GetLine
                       case Strings.span (/= ' ') cmd of
                            ("cat", file) => Pure (CatCmd (ltrim file))
                            ("copy", files) => case Strings.span (/= ' ') (ltrim files) of
                                                    (a, "") => Pure NoCmd
                                                    (a, b) => Pure (CopyCmd (ltrim a) (ltrim b))
                            ("exit", _) => Pure ExitCmd
                            _ => Pure NoCmd

mutual
  cat : (prompt : String) -> (file : String) -> ConsoleIO ()
  cat prompt file = do Right content <- ReadFile file | Left error => do PutStr (show error); shell prompt
                       PutStr content
                       shell prompt
                
  copy : (prompt : String) -> (a : String) -> (b : String) -> ConsoleIO ()
  copy prompt a b = do Right content <- ReadFile a | Left error => do PutStr (show error); shell prompt
                       WriteFile b content
                       shell prompt
  
  shell : (prompt : String) -> ConsoleIO ()
  shell prompt 
    = do input <- readInput' prompt
         case input of
              (CatCmd file) => cat prompt file
              (CopyCmd a b) => copy prompt a b
              NoCmd => shell prompt
              ExitCmd => Quit ()

partial
main' : IO ()
main' = do Just _ <- run forever (shell ">") | Nothing => putStrLn "Out of fuel"
           putStrLn "Goodbye!"
