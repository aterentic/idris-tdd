import Control.Monad.State

increase : Nat -> State Nat ()
increase inc = do current <- get
                  put (current + inc)
