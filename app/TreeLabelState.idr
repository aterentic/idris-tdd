import Control.Monad.State

data Tree a = Empty
            | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node left val right)
  = do leftLabelled <- treeLabelWith left
       (this :: rest) <- get
       put rest
       rightLabelled <- treeLabelWith right
       pure (Node leftLabelled (this, val) rightLabelled)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = evalState (treeLabelWith tree) [1..]

update : (stateType -> stateType) -> State stateType () 
update f = do state <- get
              put $ f state

increase : Nat -> State Nat ()
increase x = update (+x)

countEmpty : Tree a -> State Nat ()
countEmpty Empty = get >>= \state => put (S state)
countEmpty (Node left val right)
  = let lc = execState (countEmpty left) 0
        rc = execState (countEmpty right) 0
    in put (lc + rc)

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = get >>= \(e, n) => put (S e, n)
countEmptyNode (Node l v r) 
  = let (le, ln) = execState (countEmptyNode l) (0, 0)
        (re, rn) = execState (countEmptyNode r) (0, 0)
    in put (le + re, ln + rn + 1)

