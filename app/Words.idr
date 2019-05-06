module Words

import Data.Vect

allLengths : List String -> List Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words

export
allLengths' : Vect len String -> Vect len Nat
allLengths' [] = []
allLengths' (word :: words) = length word :: allLengths' words

