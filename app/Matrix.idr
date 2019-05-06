module Matrix

import Data.Vect

export
Matrix : (rows: Nat) -> (columns: Nat) -> Type -> Type
Matrix rows columns elem = Vect rows (Vect columns elem)

merge : Vect rows elem -> Matrix rows columns elem -> Matrix rows (S columns) elem
merge [] [] = []
merge (element :: elements) (row :: rows) = (element :: row) :: merge elements rows

transposeMatrix : Matrix rows columns elem -> Matrix columns rows elem
transposeMatrix [] = replicate _ []
transposeMatrix (firstRow :: restRows) = merge firstRow (transposeMatrix restRows)

-- Exercizes

export
transposeMatrix' : Matrix rows columns elem -> Matrix columns rows elem
transposeMatrix' [] = replicate _ []
transposeMatrix' (firstRow :: restRows) = zipWith (::) firstRow (transposeMatrix restRows)

addMatrix : Num elem => Matrix rows columns elem -> Matrix rows columns elem -> Matrix rows columns elem
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys

multSum : Num a => Vect m a -> Vect m a -> a
multSum a b = sum (zipWith (*) a b)

multRow : Num a => Matrix p m a -> Vect m a -> Vect p a
multRow b row = map (multSum row) b

multMatrix : Num a => Matrix n m a -> Matrix m p a -> Matrix n p a
multMatrix a b = map (multRow (transposeMatrix' b)) a

export
example : String
example = show $ transposeMatrix' [["1","2"], ["3","4"]]
