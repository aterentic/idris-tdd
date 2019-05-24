module Main

import System
import Data.Vect
import Average
import GettingStarted
import QuickTour
import Words
import Matrix
import Direction
import Picture
import Vehicle
import Vector
import DataStore
import Hello
import Interactive
import Printf

main01 : IO ()
main01 = do putStrLn "1 Overview"
            putStrLn "=========="
            putStrLn "Hello, Idris World!"
            putStrLn "1.4 A quick tour of Idris"
            putStrLn $ QuickTour.valToString True $ QuickTour.getStringOrInt True
            putStrLn $ QuickTour.valToString False $ QuickTour.getStringOrInt False


main02 : IO ()
main02 = do putStrLn "2 Getting started with Idris"
            putStrLn "============================"
            repl "Enter a string: " Average.showAverage
            repl "Enter a string: " (\str => (show (GettingStarted.palindrome 5 str)) ++ "\n")
            repl "Enter a string: " (\str => show (GettingStarted.counts str) ++ "\n")


main03 : IO ()
main03 = do putStrLn "3 Interactive development with types"
            putStrLn "===================================="
            putStrLn $ show $ Words.allLengths' ["First", "Second", "Third"]
            putStrLn $ Matrix.example


main04 : IO ()
main04 = do putStrLn "4 User-defined data types"
            putStrLn "========================="
            putStrLn $ show (Direction.turnClockwise North)
            putStrLn $ show Picture.example
            putStrLn $ show Vehicle.example
            putStrLn $ show (Vector.tryIndex 1 [1,2,3])
            putStrLn $ show (Vector.tryIndex 4 [1,2,3])
            putStrLn $ show (Vector.vectTake 1 [1,2,3])
            putStrLn $ show (Vector.sumEntries 1 [1,2,3] [4,5,6])
            replWith (DataStore.MkData _ [])  "Command: " DataStore.processInput



main05 : IO ()
main05 = do putStrLn "5 Interactive programms: input and output processing"
            putStrLn "===================================================="
            Hello.main
            Hello.printLonger
            Hello.printLonger'
            Just (n1, n2) <- Interactive.readNumbers | Nothing => pure ()
            putStrLn (show n1 ++ show n2)
            now <- time
            Interactive.guess (fromIntegerNat (now `mod` 100)) 0
            vect <- Interactive.readVectFile "Test.txt"
            printLn (show vect)
            
main06 : IO ()
main06 = do putStrLn "6 Programming with first-class types"
            putStrLn (Printf.printf "Hello world")

main : IO ()
main = main06
