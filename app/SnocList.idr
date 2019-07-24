module SnocList

data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])

myReverseHelper : (input : List a) -> SnocList input -> List a
myReverseHelper [] Empty = []
myReverseHelper (xs ++ [x]) (Snoc rec) = x :: myReverseHelper xs rec

snocListHelp : (snoc : SnocList input) -> (rest : List a) -> SnocList (input ++ rest)
snocListHelp {input = input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp {input = input} snoc (x :: xs) 
             = rewrite appendAssociative input [x] xs in
                       snocListHelp (Snoc snoc {x}) xs

snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs

isSuffix : Eq a => List a -> List a -> Bool
isSuffix xs ys with (snocList xs)
  isSuffix [] ys | Empty = True
  isSuffix (zs ++ [x]) ys | (Snoc xsrec) with (snocList ys)
    isSuffix (zs ++ [x]) [] | (Snoc xsrec) | Empty = False
    isSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc xsrec) | (Snoc rec) = if x == y then isSuffix zs xs | xsrec | rect else False
