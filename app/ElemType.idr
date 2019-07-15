module ElemType

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : (x : a) -> (xs : Vect k a) -> Vect (S k) a

data Elem : a -> Vect k a -> Type where
     Here : Elem x (x :: xs)
     There : (later : ElemType.Elem x xs) -> Elem x (y :: xs)

notInNil : Elem value [] -> Void
notInNil _ impossible

notInTail : (notHere : (value = x) -> Void) -> (notThere : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
isElem value [] = No notInNil
isElem value (x :: xs) = case decEq value x of
                              Yes Refl => Yes Here
                              No notHere => case isElem value xs of
                                                 Yes prf => Yes (There prf)
                                                 No notThere => No (notInTail notHere notThere)


data List' : a -> Type where
     Nil' : List' a
     Cons' : a -> List' a -> List' a
 
data Elem' : a -> List' a -> Type where
     Here' : Elem' x (Cons' x xs)
     There' : (later : Elem' x xs) -> Elem' x (Cons' y xs)

data Last : List a -> a -> Type where
     LastOne : Last [value] value
     LastCons : (prf : Last xs value) -> Last (x :: xs) value
     
-- notInNilList : Last [] value -> Void
-- notInNilList _ impossible

-- isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
-- isLast [] value = No notInNilList
-- isLast (x :: []) value = case decEq x value of
--                               Yes Refl => Yes LastOne
--                               No notSame => No (absurd ?x)
-- isLast (x :: xs) value = ?isLast_rhs_2

notInNilList : Last [] value -> Void
notInNilList _ impossible

notLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
notLast contra LastOne = contra Refl
notLast _ (LastCons _) impossible

notLastOfRest : (contra : Last xs value -> Void) -> Last (x :: xs) value -> Void
notLastOfRest contra (LastCons prf) = contra prf



isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast (x :: []) value = case decEq x value of
                              (Yes Refl) => Yes LastOne
                              (No contra) => No (notLast contra)
isLast (x :: xs) value = case isLast xs value of
                              (Yes prf) => Yes (LastCons prf)
                              (No contra) => No (notLastOfRest contra)

-- TODO functions are not total
