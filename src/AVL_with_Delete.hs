-- {-@ LIQUID "--counter-examples" @-}


module AVL_with_Delete (Tree, singleton, insert, ht, bFac) where

-- Basic functions
{-@ data Tree [rk] @-} 
data Tree a = Nil | Tree a Int (Tree a) (Tree a) deriving Show

{-@ measure ht @-}
{-@ ht :: Tree a -> Nat @-}
ht              :: Tree a -> Int
ht Nil          = 0
ht (Tree x n l r) = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

{-@ measure bFac @-}
bFac Nil          = 0
bFac (Tree v n l r) = ht l - ht r

{-@ htDiff :: s:Tree a -> t: Tree a -> {v: Int | HtDiff s t v} @-}
htDiff :: Tree a -> Tree a -> Int
htDiff l r = ht l - ht r

{-@ emp :: {v: Wavl | ht v == 0} @-}
emp = Nil

{-@ singleton :: a -> {v: Wavl | rk v == 0 }@-}
singleton a = Tree a  0 Nil Nil

{-@ measure notEmptyTree @-}
notEmptyTree :: Tree a -> Bool
notEmptyTree Nil = False
notEmptyTree _ = True

{-@ type Node0_1 = { v:AlmostWavl | notEmptyTree v && (rk v == rk.left v + 1 && rk v == rk.right v ) || 
                                    (rk v == rk.right v + 1 && rk v == rk.left v ) } @-}
-- {-@ type Node1_0 = { v:AlmostWavl | (rk v == rk.right v + 1 && rk v == rk.left v ) } @-}

{-@ type Node1_1 = { v:Wavl | notEmptyTree v && (rk v == rk.left v + 1 && rk v == rk.right v + 1)} @-}

{-@ type Node1_2 = { v:Wavl | notEmptyTree v && (rk v == rk.left v + 1 && rk v == rk.right v + 2 ) } @-}
{-@ type Node2_1 = { v:Wavl | notEmptyTree v && (rk v == rk.right v + 1 && rk v == rk.left v + 2 ) } @-}

{-@ type Node0_2 = { v:AlmostWavl | notEmptyTree v && (rk v == rk.left v && rk v == rk.right v + 2 ) } @-}
{-@ type Node2_0 = { v:AlmostWavl | notEmptyTree v && (rk v == rk.right v && rk v == rk.left v + 2 ) } @-}


{-@ measure isNode1_2 :: {v:Wavl | notEmptyTree v} -> Bool @-}
isNode1_2 :: Tree a -> Bool
isNode1_2 t@(Tree _ n l r) = (rk t == 1 + rk l) && (n == 2 + rk r) 
isNode1_2 Nil = error "need a tree not empty" 

{-@ measure isNode2_1 :: {v:Wavl | notEmptyTree v} -> Bool @-}
isNode2_1 :: Tree a -> Bool
isNode2_1 t@(Tree _ n l r) = (rk t == 2 + rk l) && (n == 1 + rk r)  
isNode2_1 Nil = error "need a tree not empty" 

{-@ measure isNode1_1 :: {v:Wavl | notEmptyTree v} -> Bool @-}
isNode1_1 :: Tree a -> Bool
isNode1_1 t@(Tree _ n l r) = (rk t == 1 + rk l) && (n == 1 + rk r)  
isNode1_1 Nil = error "need a tree not empty" 


-- | Insert functions

{-@ decrease insert 3 @-}
{-@ insert :: a -> s:Wavl -> {t:Wavl | notEmptyTree t && ( (EqRk s t) || (RkDiff t s 1) ) } @-}
insert :: (Ord a) => a -> Tree a -> Tree a
insert x Nil = singleton x
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> insR
    EQ -> t
    where r' = insert x r
          l' = insert x l
          lt' = Tree v n l' r
          rt' = Tree v n l r'
          insL | rk l' < n = lt'
               | rk l' == rk r + 1 = promote lt'
               | otherwise = case l' of
                  (Tree y m a b) -> if rk b + 2 == m then rotateRight lt'
                    else rotateDoubleRight lt'
                  _ -> error "tree not matched at insL"
          insR | rk r' < n = rt'
               | rk r' == rk l + 1 = promote rt'
               | otherwise = case r' of
                (Tree y m b c) -> if rk b +2 == m then rotateLeft rt'
                  else rotateDoubleLeft rt'
                _ -> error "tree not matched at insR"



{-@ promote :: Node0_1 -> Wavl @-}
promote :: Tree a -> Tree a
promote (Tree a n l r) = (Tree a (n+1) l r)
promote Nil = error "NIL cannot be promoted"

{-@ rotateRight :: {v:Node0_2 | IsNode1_2 (left v) } -> {t:Node1_1 | isNode1_1 (right t) && EqRk v t } @-}
rotateRight :: Tree a -> Tree a
rotateRight t@(Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)
rotateRight _ = error "Tree did not match criteria"

{-@ rotateDoubleLeft :: {v:Node2_0 | IsNode1_2 (right v) } -> {t:Node1_1 | EqRk v t } @-}
rotateDoubleLeft :: Tree a -> Tree a
rotateDoubleLeft t@(Tree x n a (Tree y m (Tree z o b_1 b_2) c)) =
  Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 
rotateDoubleLeft _ = error "Tree did not match criteria"

{-@ rotateLeft :: {v:Node2_0 | IsNode2_1 (right v) } -> {t:Node1_1 | isNode1_1 (left t) && EqRk v t } @-}
rotateLeft :: Tree a -> Tree a
rotateLeft t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c
rotateLeft _ = error "Tree did not match criteria"

{-@ rotateDoubleRight :: {v:Node0_2 | IsNode2_1 (left v) } -> {t:Node1_1 | EqRk v t } @-}
rotateDoubleRight :: Tree a -> Tree a
rotateDoubleRight t@(Tree x n (Tree y m a (Tree z o b_1 b_2)) c) = 
  Tree z (o+1) (Tree y (m-1) a b_1) (Tree  x (n-1) b_2 c) 
rotateDoubleRight _ = error "Tree did not match criteria"

-- Delete



-- Test
main = do
    mapM_ print [a,b,c,d]
  where
    a = singleton 5
    b = insert 2 a
    c = insert 3 b
    d = insert 7 c

-- Liquid Haskell

{-@ predicate HtDiff S T D = (ht S) - (ht T) == D @-}
{-@ predicate EqHt S T = (ht S) == (ht T) @-}

{-@ predicate LeftHeavy T = bFac T == 1 @-}
{-@ predicate RightHeavy T = bFac T == -1 @-}

-- predicates by me
{-@ predicate EqRk S T = rk T == rk S @-}
{-@ predicate RkDiff S T D = (rk S) - (rk T) == D @-}

{-@ measure rkDiff @-}
rkDiff :: Int -> Tree a -> Int -> Bool
rkDiff n s d = n - (rk s) == d

{-@ measure not2_2Node :: Rank -> Wavl -> Wavl -> Bool @-}
not2_2Node :: Int -> Tree a -> Tree a -> Bool
not2_2Node n l r = ( (rkDiff n r 2) ==> rkDiff nl 1) && ((rkDiff n l 2) ==> (rkDiff n r 1))

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced Nil = True
balanced t@(Tree _ n l r) = rk r < n && n <= rk r + 2 
                       && rk l < n && n <= rk l + 2
                       && not2_2Node n l r -- this term is only allowed with insertion only trees
                       && (balanced l)
                       && (balanced r)

-- my additions
{-@ type Rank = {v:Int | v >= -1 } @-}
{-@ type AlmostWavl = {t:Tree | (notEmptyTree t) ==> (balanced (left t) && balanced (right t)) } @-}

-- {-@ measure left :: {t:Tree | notEmptyTree t } -> Tree @-}
{-@ measure left :: {t:Tree | notEmptyTree t } -> Tree @-}
left :: Tree a -> Tree a
left Nil = error "Nothing to return"
left (Tree _ _ l _) = l

{-@ measure right :: {t:Tree | notEmptyTree t } -> Tree @-}
right :: Tree a -> Tree a
right Nil = error "Nothing to return"
right (Tree _ _ _ r) = r

{-@ measure rk @-}
{-@ rk :: Tree a -> Rank @-}
rk :: Tree a -> Int
rk Nil =  -1
rk (Tree _ n _ _) = n

{-@ type Wavl = {v: Tree a | balanced v} @-}
