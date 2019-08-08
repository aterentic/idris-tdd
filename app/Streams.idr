 import Data.Primitives.Views

labelFrom : Integer -> List a -> List (Integer, a)
labelFrom n [] = []
labelFrom n (x :: xs) = (n, x) :: labelFrom (n + 1) xs

label : List a -> List (Integer, a)
label = labelFrom 0

data InfList : Type -> Type where
     (::) : (value : a) -> Inf (InfList a) -> InfList a

%name InfList xs, ys, zs

countFrom : Integer -> InfList Integer
countFrom n = n :: Delay (countFrom (n + 1))

getPrefix : (count : Nat) -> InfList a -> List a
getPrefix Z xs = []
getPrefix (S k) (value :: values) = value :: getPrefix k values

labelWith : Stream lt -> List a -> List (lt, a)
labelWith lbs [] = []
labelWith (lb :: lbs) (x :: xs) = (lb, x) :: labelWith lbs xs

label' : List a -> List (Integer, a)
label' = labelWith (iterate (+1) 0)

Functor InfList where
  map func (value :: xs) = (func value) :: map func xs
