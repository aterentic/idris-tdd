data Tree elem = Empty | Node (Tree elem) elem (Tree elem)

%name Tree tree, tree1, tree2

insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x tree@(Node left y right) = case compare x y of
                                    LT => Node (insert x left) y right
                                    EQ => tree
                                    GT => Node left y (insert x right)

data BSTree : Type -> Type where
     BSEmpty : Ord elem => BSTree elem
     BSNode : Ord elem => (left : BSTree elem) -> (val : elem) -> (right : BSTree elem) -> BSTree elem

bsinsert : elem -> BSTree elem -> BSTree elem
bsinsert x BSEmpty = BSNode BSEmpty x BSEmpty
bsinsert x tree@(BSNode left y right) = case compare x y of
                                    LT => BSNode (bsinsert x left) y right
                                    EQ => tree
                                    GT => BSNode left y (bsinsert x right)

-- Exercises

listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)

treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node left x right) = (treeToList left) ++ [x] ++ (treeToList right)

data IntegerExpression = Val Integer 
                       | Add IntegerExpression IntegerExpression
                       | Sub IntegerExpression IntegerExpression
                       | Mul IntegerExpression IntegerExpression
                       

evaluate : IntegerExpression -> Integer                       
evaluate (Val x) = x
evaluate (Add x y) = evaluate x + evaluate y
evaluate (Sub x y) = evaluate x - evaluate y
evaluate (Mul x y) = evaluate x * evaluate y

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing y = y
maxMaybe x Nothing = x
maxMaybe (Just x) (Just y) = if x > y then Just x else Just y


