data RunIO : Type -> Type where
     Quit : a -> RunIO a
     Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b

(>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
(>>=) = Do

greet : RunIO ()
greet = do putStr "Enter your name: "
           name <- getLine
           if name == ""
              then putStrLn "Bye bye!" >>= \_ => Delay (Quit ())
              else putStrLn ("Hello " ++ name) >>= \_ => Delay greet
