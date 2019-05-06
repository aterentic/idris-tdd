import Data.Vect

insert : Ord elem => (x : elem) -> (sorted : Vect len elem) -> Vect (S len) elem
insert x [] = [x]
insert x (y :: xs) = if x < y then x :: y :: xs else y :: insert x xs

insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) = insert x (insSort xs)

-- Exercises

my_length : List a -> Nat
my_length [] = Z
my_length (x :: xs) = S (my_length xs)

my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) = (my_reverse xs) ++ [x]

my_map : (a -> b) -> List a -> List b
my_map f [] = []
my_map f (x :: xs) = f x :: my_map f xs

my_map1 : (a -> b) -> Vect n a -> Vect n b
my_map1 f [] = []
my_map1 f (x :: xs) = f x :: my_map1 f xs
