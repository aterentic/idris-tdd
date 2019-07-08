module Fold

totalLen : List String -> Nat
totalLen xs = foldr (\elem, acc => acc + length elem) 0 xs
