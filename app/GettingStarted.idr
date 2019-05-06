module GettingStarted

export
palindrome : (longerThan : Nat) -> String -> Bool
palindrome min str =
  let 
    insensitive = toLower str 
    longer = length str > min in
    longer && insensitive == (reverse insensitive)
    
||| Returns a pair of the number of words and characters in the input
export    
counts : String -> (Nat, Nat)
counts str = (length (words str), length str)

||| Returns ten larges values in a list
export
top_ten : Ord a => List a -> List a
top_ten a = take 10 (reverse (sort a))

||| Returns number of strings in the list longer than the given number of characters
export
over_length : Nat -> List String -> Nat
over_length limit strs =
  sum (map (\e => if (length e > limit) then 1 else 0) strs)


-- Function types and definitions
double : (value : Int) -> Int
double x = x + x
  
-- Partially applying functions
add : Int -> Int -> Int
add x y = x + y

-- Writing generic functions: variables in types
identity : ty -> ty
identity x = x

the : (ty : Type) -> ty -> ty
the ty x = x

double' : Num ty => ty -> ty
double' x = x + x

-- Higher-order function types
twice : (a -> a) -> a -> a
twice f x = f (f x)

-- Local definitions: let and where
longer : String -> String -> Nat
longer w1 w2
  = let l1 = length w1
        l2 = length w2 in
        if l1 > l2 then l1 else l2
        
pythagoras : Double -> Double -> Double
pythagoras x y = sqrt (square x + square y)
  where
    square : Double -> Double
    square x = x * x
