import Data.Vect

%default total

data StackCmd : Type -> Nat -> Nat -> Type where
     Push : Integer -> StackCmd () height (S height)
     Pop  : StackCmd Integer (S height) height
     Top  : StackCmd Integer (S height) (S height)
     
     GetStr : StackCmd String height height
     PutStr : String -> StackCmd () height height
     
     Pure : ty -> StackCmd ty height height
     (>>=): StackCmd a height1 height2 ->
            (a -> StackCmd b height2 height3) ->
            StackCmd b height1 height3

testAdd : StackCmd Integer 0 0
testAdd = do Push 10
             Push 20
             val1 <- Pop
             val2 <- Pop
             Pure (val1 + val2)

runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           IO (ty, Vect outHeight Integer)
runStack stk (Push val) = pure ((), val :: stk)
runStack (val :: rest) Pop = pure (val, rest)
runStack (val :: rest) Top = pure (val, val::rest)

runStack stk GetStr = do x <- getLine
                         pure (x, stk)
runStack stk (PutStr val) = do putStr val
                               pure ((), stk)
runStack stk (Pure val) = pure (val, stk)
runStack stk (x >>= f) = do (x', new) <- runStack stk x
                            runStack new (f x')

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do val1 <- Pop
           val2 <- Pop
           Push (val1 + val2)

doSubstract : StackCmd () (S (S height)) (S height)
doSubstract = do val1 <- Pop
                 val2 <- Pop
                 Push (val2 - val1)

doMultiply : StackCmd () (S (S height)) (S height)
doMultiply = do val1 <- Pop
                val2 <- Pop
                Push (val1 * val2)

doNegate : StackCmd () (S height) (S height)
doNegate = do val <- Pop
              Push (0 - val)

doDiscard : StackCmd Integer (S height) height
doDiscard = do val <- Pop
               Pure val

doDuplicate : StackCmd Integer (S height) (S (S height))
doDuplicate = do val <- Top
                 Push val
                 Pure val

data StackIO : Nat -> Type where
     Do : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) ->
          StackIO height1

namespace StackDo
  (>>=) : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) ->
          StackIO height1
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run (More fuel) stk (Do c f)
  = do (res, newStk) <- runStack stk c
       run fuel newStk (f res)
run Dry stk p = pure ()

data StkInput = Number Integer
              | Add
              | Substract
              | Multiply
              | Negate
              | Discard
              | Duplicate

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "sub" = Just Substract
strToInput "mul" = Just Multiply
strToInput "neg" = Just Negate
strToInput "dis" = Just Discard
strToInput "dup" = Just Duplicate
strToInput x = if all isDigit (unpack x)
               then Just (Number (cast x))
               else Nothing


mutual
  tryAdd : StackIO height
  tryAdd {height = (S (S h))} 
         = do doAdd
              result <- Top
              PutStr (show result ++ "\n")
              stackCalc
  tryAdd = do PutStr "Fewer than two items on the stack\n"
              stackCalc

  trySubstract : StackIO height
  trySubstract {height = (S (S h))} 
         = do doSubstract
              result <- Top
              PutStr (show result ++ "\n")
              stackCalc
  trySubstract = do PutStr "Fewer than two items on the stack\n"
                    stackCalc

  tryMultiply : StackIO height
  tryMultiply {height = (S (S h))} 
         = do doMultiply
              result <- Top
              PutStr (show result ++ "\n")
              stackCalc
  tryMultiply = do PutStr "Fewer than two items on the stack\n"
                   stackCalc

  tryNegate : StackIO height
  tryNegate {height = (S h)} 
         = do doNegate
              result <- Top
              PutStr (show result ++ "\n")
              stackCalc
  tryNegate = do PutStr "Fewer than one item on the stack\n"
                 stackCalc

  tryDiscard : StackIO height
  tryDiscard {height = S h} 
         = do result <- doDiscard
              PutStr ("Discarded " ++ show result ++ "\n")
              stackCalc
  tryDiscard = do PutStr "Fewer than one item on the stack\n"
                  stackCalc

  tryDuplicate : StackIO height
  tryDuplicate {height = S h} 
         = do result <- doDuplicate
              PutStr ("Duplicated " ++ show result ++ "\n")
              stackCalc
  tryDuplicate = do PutStr "Fewer than one item on the stack\n"
                    stackCalc
  
  
  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                      Nothing => do PutStr "Invalid input\n"
                                    stackCalc
                      Just (Number x) => do Push x
                                            stackCalc
                      Just Add => tryAdd
                      Just Substract => trySubstract
                      Just Multiply => tryMultiply
                      Just Negate => tryNegate
                      Just Discard => tryDiscard
                      Just Duplicate => tryDuplicate

partial
main : IO ()
main = run forever [] stackCalc
