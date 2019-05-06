module Hello

printLength : IO ()
printLength = getLine >>= \input => let len = length input in 
                                     putStrLn (show len)
                                     
                                     
max : Int -> Int -> Int
max a b = if a > b then a else b

export
printLonger : IO ()
printLonger = do putStr "Enter first string: "
                 x <- getLine
                 putStr "Enter second string: "
                 y <- getLine
                 putStrLn $ "Length of longer is: " ++ show (max (length x) (length y))

export
printLonger' : IO ()
printLonger' = putStr "Enter first string: " >>= \_ =>
               getLine >>= \x =>
               putStr "Enter second string: " >>= \_ =>
               getLine >>= \y =>
               putStrLn $ "Length of longer is: " ++ show (max (length x) (length y))
                

export
main : IO ()
main = do
  putStr "Enter your name: "
  x <- getLine
  putStrLn ("Hello " ++ x ++ "!")

