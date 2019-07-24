module DescribeList

describeList : List Int -> String
describeList [] = "Empty"
describeList (x :: xs) = "Non-empty, tail = " ++ show xs

data ListLast : List a -> Type where
     Empty : ListLast []
     NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

total
describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Non-empty, initial portion = " ++ show xs

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of 
                          Empty => NonEmpty [] x
                          (NonEmpty ys y) => NonEmpty (x :: ys) y

total
describeListEnd : List Int -> String
describeListEnd xs = describeHelper xs (listLast xs)

total
describeListEnd' : List Int -> String
describeListEnd' input with (listLast input)
  describeListEnd' [] | Empty = "Empty"
  describeListEnd' (xs ++ [y]) | (NonEmpty xs y) = "Non-empty, initial portion = " ++ show xs

myReverse : List a -> List a
myReverse input with (listLast input)
  myReverse [] | Empty = []
  myReverse (xs ++ [x]) | (NonEmpty xs x) = x :: myReverse xs

 
data SplitList : List a -> Type where
     SplitNil : SplitList []
     SplitOne : SplitList [x]
     SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

total 
splitList : (input : List a) -> SplitList input
splitList input = helper input input
  where
    helper : List a -> (input : List a) -> SplitList input
    helper _ [] = SplitNil
    helper _ [x] = SplitOne
    helper (_ :: _ :: counter) (item :: items)
      = case helper counter items of
             SplitNil => SplitOne
             SplitOne {x} => SplitPair [item] [x]
             SplitPair lefts rights => SplitPair (item :: lefts) rights
    helper _ items = SplitPair [] items

mergeSort : Ord a => List a -> List a
mergeSort input with (splitList input)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights) 
            = merge (mergeSort lefts) (mergeSort rights)

data TakeN : List a -> Type where
     Fewer : TakeN xs
     Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z _ = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             (Exact n_xs) => Exact (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest


halves : (xs : List a) -> (List a, List a)
halves input with (takeN (div (length input) 2) input)
  halves input | Fewer = ([], input)
  halves (n_xs ++ rest) | Exact n_xs = (n_xs, rest)

data SnocList ty = EmptySnoc | Snoc (SnocList ty) ty
                
reverseSnoc : SnocList ty -> List ty
reverseSnoc EmptySnoc = []
reverseSnoc (Snoc xs x) = x :: reverseSnoc xs

