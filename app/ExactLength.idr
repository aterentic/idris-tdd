module ExactLength

data Vect : Nat -> Type -> Type where
     Nil : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
     Same : (num : Nat) -> EqNat num num

sameS : {k : Nat} -> {j : Nat} -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS (Same k) = Same (S k)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same Z)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              Just eq => Just (sameS eq)

checkEqNat' : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat' Z Z = Just (Same Z)
checkEqNat' Z (S k) = Nothing
checkEqNat' (S k) Z = Nothing
checkEqNat' (S k) (S j) = case checkEqNat' k j of
                              Nothing => Nothing
                              Just (Same k) => Just (Same (S k))

checkEqNat'' : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat'' Z Z = Just (Same Z)
checkEqNat'' Z (S k) = Nothing
checkEqNat'' (S k) Z = Nothing
checkEqNat'' (S k) (S j) = do (Same k) <- checkEqNat'' k j 
                              Just (Same (S k))


checkEqNat''' : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat''' Z Z = Just Refl
checkEqNat''' Z (S k) = Nothing
checkEqNat''' (S k) Z = Nothing
checkEqNat''' (S k) (S j) = do prf <- checkEqNat''' k j 
                               Just (cong prf)

exactLength : (len1 : Nat) -> (input : Vect len2 a) -> Maybe (Vect len1 a)
exactLength len1 {len2} input = checkEqNat len1 len2 >>= \(Same _) => Just input

data Equal : a -> b -> Type where
     Reflex : Equal x x

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons prf = cong prf

same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl prf2 = same_cons prf2

data ThreeEq : a -> b -> c -> Type where
     ThreeRefl : ThreeEq x x x

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)     
allSameS z z z ThreeRefl = the (ThreeEq (S z) (S z) (S z)) ThreeRefl
