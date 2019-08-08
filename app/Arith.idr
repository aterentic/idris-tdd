import Data.Primitives.Views

quiz : Stream Int -> (score : Nat) -> IO ()
quiz (num1 :: num2 :: nums) score 
  = do putStrLn ("Score so far: " ++ show score)
       putStrLn (show num1 ++ " * " ++ show num2 ++ "? ")
       answer <- getLine
       if cast answer == num1 * num2
       then do putStrLn "Correct!"
               quiz nums (score + 1)
       else do putStrLn ("Wrong, the answer is " ++ show (num1 * num2))
               quiz nums score

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 101390423 in
                   (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound num with (divides num 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

every_other : Stream a -> Stream a
every_other (first :: second :: xs) = second :: every_other xs


data Face = Heads | Tail

total
getFace : Int -> Face
getFace x with (divides x 2)
  getFace ((2 * div) + rem) | (DivBy prf) = if rem == 0 then Heads else Tail

total
coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z xs = []
coinFlips (S k) (value :: xs) = getFace value :: coinFlips k xs

square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx = approx :: square_root_approx number ((approx + (number / approx)) / 2)

square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) -> (approxs : Stream Double) -> Double
square_root_bound Z number bound (approx :: approxs) = approx
square_root_bound (S k) number bound (approx :: approxs) 
  = if (approx * approx) < bound then approx else square_root_bound k number bound approxs

square_root : (number : Double) -> Double
square_root number = square_root_bound 100 number 0.00000000001
                                       (square_root_approx number number)
