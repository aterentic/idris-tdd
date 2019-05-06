module Vector

import Data.Vect
import Data.Fin

data Vect : Nat -> Type -> Type where
     Nil  : Vector.Vect Z a
     (::) : (x : a) -> (xs : Vector.Vect k a) -> Vector.Vect (S k) a
     
%name Vector.Vect xs, ys, zs     

append : Vector.Vect n elem -> Vector.Vect m elem -> Vector.Vect (n + m) elem
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

zip : Vector.Vect n a -> Vector.Vect n b -> Vector.Vect n (a, b)
zip [] ys = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

export
tryIndex : Integer -> Data.Vect.Vect n a -> Maybe a
tryIndex {n} x xs = case integerToFin x n of
                         Nothing => Nothing
                         (Just idx) => Just (Data.Vect.index idx xs)

export
vectTake : (m : Fin n) -> Data.Vect.Vect n a -> Data.Vect.Vect (finToNat m) a
vectTake FZ xs = []
vectTake (FS x) (y :: xs) = y :: vectTake x xs

export
sumEntries : Num a => (pos : Integer) -> Data.Vect.Vect n a -> Data.Vect.Vect n a -> Maybe a
sumEntries pos [] [] = Nothing
sumEntries {n} i xs ys = case integerToFin i n of
                              Nothing => Nothing
                              Just pos => Just (index pos xs + index pos ys)
