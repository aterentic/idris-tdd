module ReverseVect

import Data.Vect

myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse (x :: xs) = reverseProof (myReverse xs ++ [x])
  where
    reverseProof : Vect (k + 1) elem -> Vect (S k) elem
    reverseProof {k} result = rewrite plusCommutative 1 k in result

myReverse' : Vect length elemType -> Vect length elemType
myReverse' xs = reverse' [] xs
  where reverse' : Vect n elemType -> Vect m elemType -> Vect (n + m) elemType
        reverse' {n} acc [] = rewrite plusZeroRightNeutral n in acc
        reverse' {n = S n'} {m = S m'} acc (x :: xs) 
                        = rewrite sym (plusSuccRightSucc n' m') in reverse' (x::acc) xs
