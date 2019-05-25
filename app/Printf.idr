module Printf

import Data.Vect

data Format = Number Format
            | Str Format
            | Chr Format
            | Dbl Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number fmt) = Int -> PrintfType fmt
PrintfType (Str fmt) = String -> PrintfType fmt
PrintfType (Chr fmt) = Char -> PrintfType fmt
PrintfType (Dbl fmt) = Double -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Chr fmt) acc = \c => printfFmt fmt (acc ++ "'" ++ cast c ++ "'")
printfFmt (Dbl fmt) acc = \d => printfFmt fmt (acc ++ show d)
printfFmt (Lit str fmt) acc = printfFmt fmt (acc ++ str)
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Chr (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Dbl (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of 
                             Lit str fmt' => Lit (cast c ++ str) fmt'
                             fmt' => Lit (cast c) fmt'

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

-- Exercise 1

Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)

testMatrix : Matrix 2 3
testMatrix = [[0,0,0],[0,0,0]]

-- Exercise 3

TupleVect : Nat -> Type -> Type
TupleVect Z elem = ()
TupleVect (S k) elem = (elem, TupleVect k elem)

test : TupleVect 4 Nat
test = (1,2,3,4,())

export
main : IO ()
main = putStrLn (printf "Hello %d. %s" 1 "world")
