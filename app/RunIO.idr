%default total

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

data Fuel = Dry | More (Lazy Fuel)

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

partial
forever : Fuel
forever = More forever

run : Fuel -> RunIO a -> IO (Maybe a)
run fuel (Quit x) = pure (Just x)
run (More fuel) (Do c f) = do res <- c
                              run fuel (f res)
run Dry p = pure Nothing

partial
main : IO ()
main = do run forever greet
          pure ()
