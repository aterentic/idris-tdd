module TypeFuns

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "Hello world"
getStringOrInt True = 1

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False x = trim x
valToString True x = cast x

valToString' : (isInt : Bool) -> (case isInt of 
                                           False => String
                                           True => Int) -> String
valToString' False x = trim x
valToString' True x = cast x

-- non total functions at type level don't evaluate further

AdderType : (numargs : Nat) -> Type -> Type
AdderType Z numtype = numtype
AdderType (S k) numtype = (next : numtype) -> AdderType k numtype

adder : Num numtype => (numargs : Nat) -> (acc : numtype) -> AdderType numargs numtype
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

