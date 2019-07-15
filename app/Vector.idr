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

Eq ty => Eq (Vector.Vect len ty) where
  (==) [] [] = True  
  (==) (x :: xs) (y :: ys) = x == y && xs == ys

Foldable (Vector.Vect len) where
  foldr func init [] = init
  foldr func init (x :: xs) = foldr func (func x init) xs
  foldl func init [] = init
  foldl func init (x :: xs) = func (foldl func init xs) x


headUnequal : DecEq a => {xs : Vector.Vect n a} -> {ys : Vector.Vect n a} -> (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl



tailUnequal : DecEq a => {xs : Vector.Vect n a} -> {ys : Vector.Vect n a} -> (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

DecEq a => DecEq (Vector.Vect n a) where  
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = case decEq x y of
                                   (Yes Refl) => case decEq xs ys of
                                                      (Yes Refl) => Yes Refl
                                                      (No contra) => No (tailUnequal contra)
                                   (No contra) => No (headUnequal contra)

removeElem : (value : a) -> (xs : Data.Vect.Vect (S n) a) -> (prf : Elem value xs) -> Data.Vect.Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later) = y :: removeElem value ys later

removeElem_auto : (value : a) -> (xs : Data.Vect.Vect (S n) a) -> {auto prf : Elem value xs} -> Data.Vect.Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf


maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

removeElem' : (value : a) -> (xs : Data.Vect.Vect (S n) a) -> {auto prf : Elem value xs} -> Data.Vect.Vect n a
removeElem' value (value :: ys) {prf = Here} = ys
removeElem' {n = Z} value (y :: []) {prf = (There later)} = absurd later
removeElem' {n = (S k)} value (y :: ys) {prf = (There _)} = y :: removeElem' value ys 


