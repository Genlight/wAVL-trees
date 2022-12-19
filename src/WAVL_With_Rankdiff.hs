{- Example of AVL trees by michaelbeaumont -}

-- {-@ LIQUID "--short-names" @-}

module WAVL_With_Rankdiff (Tree, initialT, insert) where

-- define Orderedness
{-@ type TreeL a X = Tree {v:a | v < X }  @-}
{-@ type TreeR a X = Tree {v:a | X < v }  @-}


-- Basic functions
{-@ data Tree [ht] @-}
data Tree a = Nil Int | Tree a Int (Tree a) (Tree a) deriving Show

{-@ type RankDiff = {v:Int |  0 <= v && v <= 3 }  @-} -- TODO: change back to <= 3
{-@ type NilRank = {v:Int |  1 <= v && v <= 2 }  @-} 

-- pathlength
{-@ measure plen @-}
{-@ plen :: Tree a -> Nat @-}
plen              :: Tree a -> Int
plen (Nil 1)         = 0
plen (Nil 2)         = 1
plen (Tree _ n l _) = n + plen l

{-@ measure ht @-}
{-@ ht :: Tree a -> Nat @-}
ht              :: Tree a -> Int
ht (Nil _)         = 0
ht (Tree x n l r) = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

{-@ measure bFac @-}
bFac (Nil _)         = 0
bFac (Tree v n l r) = ht l - ht r

{-@ htDiff :: s:Tree a -> t: Tree a -> {v: Int | HtDiff s t v} @-}
htDiff :: Tree a -> Tree a -> Int
htDiff l r = ht l - ht r

{-@ initialT :: a -> Wavl @-}
initialT :: a -> Tree a
initialT a = singleton a 0

{-@ emp :: {t:Wavl | plen t == 1 } @-}
emp = Nil 1

{-@ singleton :: a -> {v:RankDiff | v== 0 || v == 1 } -> Wavl @-}
singleton :: a -> Int -> Tree a
singleton a n = Tree a n (Nil 1) (Nil 1)

{-@ measure notEmptyTree :: Tree a -> Bool @-}
notEmptyTree :: Tree a -> Bool
notEmptyTree (Tree _ _ _ _) = True
notEmptyTree (Nil _) = False

{-@ type NETree = {t:Tree | notEmptyTree t } @-}

{-@ type Node0_1 = { v:AlmostWavl | notEmptyTree v && (rd (left v) == 0 && rd (right v) == 1) } @-}
{-@ type Node1_0 = { v:AlmostWavl | notEmptyTree v && (rd (left v) == 1 && rd (right v) == 0) } @-}

{-@ type Node1_1 = { v:Wavl | notEmptyTree v && (rd (left v) == 1 && rd (right v) == 1) } @-}

{-@ type Node1_2 = { v:Wavl | notEmptyTree v && (rd (left v) == 1 && rd (right v) == 2) } @-}
{-@ type Node2_1 = { v:Wavl | notEmptyTree v && (rd (left v) == 2 && rd (right v) == 1) } @-}

{-@ type Node0_2 = { v:AlmostWavl | notEmptyTree v && (rd (left v) == 0 && rd (right v) == 2) } @-}
{-@ type Node2_0 = { v:AlmostWavl | notEmptyTree v && (rd (left v) == 2 && rd (right v) == 0) } @-}


{-@ measure isNode1_2 :: {v:Wavl | notEmptyTree v} -> Bool @-}
isNode1_2 :: Tree a -> Bool
isNode1_2 (Tree _ n l r) = (rd l == 1) && (rd r == 2) 
isNode1_2 _ = error "need a tree not empty" 

{-@ measure isNode2_1 :: {v:Wavl | notEmptyTree v} -> Bool @-}
isNode2_1 :: Tree a -> Bool
isNode2_1 (Tree _ n l r) = (rd l == 2) && (rd r == 1) 
isNode2_1 _ = error "need a tree not empty" 

-- | Insert functions
{-@ decrease insert 3 @-}
{-@ insert :: a -> s: Wavl -> {t:Wavl | notEmptyTree t } @-}
insert :: (Ord a) => a -> Tree a -> Tree a
insert x (Nil 1) = singleton x 0
insert x (Nil 2) = singleton x 1
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> insR
    EQ -> t
    where r' = insert x r
          l' = insert x l
          insL | rd l' > 0 = (Tree v n l' r)
               | rd l' + 1 == rd r = promoteL v n l' r
               | rd (right l') == 2 = rotateRight v n l' r
               | rd (right l') == 1 = rotateDoubleRight v n l' r
               | otherwise = error "tree not matched at insL"
          insR | rd r' > 0 = (Tree v n l r')
               | rd r' + 1 == rd l = promoteR v n l r'
               | rd (left r') == 2 = rotateLeft v n l r'
               | rd (left r') == 1 = rotateDoubleLeft v n l r'
               | otherwise = error "tree not matched at insR"

{-@ type RdNode = {v:Int | v<= 1 && v <= 2} @-}

-- rankdiffs for promote: multiple changes happen, namely the promoted node's rd gets reduced by 1, and both children rd get increased
{-@ promoteR :: a -> rn:RdNode -> {l:Wavl | rd l == 1 } -> {r:Wavl | (rd r == 0) && ((isNode1_2 r) || (isNode2_1 r))} -> Wavl @-}
promoteR :: a -> Int -> Tree a -> Tree a -> Tree a
promoteR a n (Nil 1) (Tree ar 0 lr rr)           = (Tree a (n-1) (Nil 2) (Tree ar 1 lr rr))
promoteR a n (Tree al 1 ll lr) (Tree ar 0 rl rr) = (Tree a (n-1) (Tree al 2 ll lr) (Tree ar 1 rl rr))

{-@ promoteL :: a -> rn:RdNode -> {l:Wavl | ((isNode1_2 l) || (isNode2_1 l)) && (rd l == 0) } -> {r:Wavl | rd r == 0} -> Wavl @-}
promoteL :: a -> Int -> Tree a -> Tree a -> Tree a
promoteL a n (Tree al 0 ll lr) (Nil 1) = (Tree a (n-1) (Tree al 1 ll lr) (Nil 2))
promoteL a n (Tree al 0 ll lr) (Tree ar 1 rl rr) = (Tree a (n-1) (Tree al 1 ll lr) (Tree ar 2 rl rr))


{-@ rotateRight :: a -> RdNode -> {l:Node1_2 | rd l == 0} -> {r:Wavl | rd r == 2} -> Wavl @-}
rotateRight :: (Ord a) => a -> Int -> Tree a -> Tree a -> Tree a
rotateRight x n (Tree y 0 a@(Tree _ 1 _ _) (Tree bv 2 bl br)) (Tree z 2 c d) = Tree y n a (Tree x 1 (Tree bv 1 bl br) (Tree z 1 c d))
rotateRight x n (Tree y 0 a@(Tree _ 1 _ _) (Tree bv 2 bl br)) (Nil 2)        = Tree y n a (Tree x 1 (Tree bv 1 bl br) (Nil 1))
rotateRight x n (Tree y 0 a@(Tree _ 1 _ _) (Nil 2)) (Tree z 2 c d)           = Tree y n a (Tree x 1 (Nil 1) (Tree z 1 c d))
rotateRight x n (Tree y 0 a@(Tree _ 1 _ _) (Nil 2)) (Nil 2)                  = Tree y n a (Tree x 1 (Nil 1) (Nil 1))
rotateRight _ _ _ _ = error "Tree did not match criteria"

{-@ rotateLeft :: a -> RdNode -> {l:Wavl | rd l == 2} -> {r:Node2_1 | rd r == 0} -> Wavl @-}
rotateLeft :: (Ord a) => a -> Int -> Tree a -> Tree a -> Tree a
rotateLeft x n a@(Tree av 2 al ar) (Tree y 0 (Tree bv 2 bl br) c@(Tree _ 1 _ _)) = Tree y n (Tree x 1 (Tree av 1 al ar) (Tree bv 1 bl br)) c
rotateLeft x n a@(Tree av 2 al ar) (Tree y 0 (Nil 2) c@(Tree _ 1 _ _)) = Tree y n (Tree x 1 (Tree av 1 al ar) (Nil 1)) c
rotateLeft x n (Nil 2) (Tree y 0 (Tree bv 2 bl br) c@(Tree _ 1 _ _)) = Tree y n (Tree x 1 (Nil 1) (Tree bv 1 bl br)) c
rotateLeft x n (Nil 2) (Tree y 0 (Nil 2) c@(Tree _ 1 _ _)) = Tree y n (Tree x 1 (Nil 1) (Nil 1)) c
rotateLeft _ _ _ _ = error "Tree did not match criteria"

{-@ rotateDoubleRight :: a -> RdNode -> {l:Node1_2 | rd l == 0 } -> {r:Wavl | rd r == 2 } -> Wavl @-}
rotateDoubleRight :: (Ord a) => a -> Int -> Tree a -> Tree a -> Tree a
rotateDoubleRight x n (Tree y 0 (Tree av 2 al ar) (Tree z 1 b_1 b_2)) (Tree cv 2 cl cr) = Tree z n (Tree y 1 (Tree av 1 al ar) b_1) (Tree x 1 b_2 (Tree cv 1 cl cr)) 
rotateDoubleRight x n (Tree y 0 (Tree av 2 al ar) (Tree z 1 b_1 b_2)) (Nil 2)           = Tree z n (Tree y 1 (Tree av 1 al ar) b_1) (Tree x 1 b_2 (Nil 1)) 
rotateDoubleRight x n (Tree y 0 (Nil 2) (Tree z 1 b_1 b_2)) c@(Tree cv 2 cl cr)         = Tree z n (Tree y 1 (Nil 1) b_1) (Tree  x 1 b_2 (Tree cv 1 cl cr)) 
rotateDoubleRight x n (Tree y 0 (Nil 2) (Tree z 1 b_1 b_2)) (Nil 2)                     = Tree z n (Tree y 1 (Nil 1) b_1) (Tree  x 1 b_2 (Nil 1)) 
rotateDoubleRight _ _ _ _ = error "Tree did not match criteria"

{-@ rotateDoubleLeft :: a -> RdNode -> {l:Wavl | rd l == 2} -> {r:Node1_2 | rd r == 0} -> Wavl @-}
rotateDoubleLeft :: (Ord a) => a -> Int -> Tree a -> Tree a -> Tree a
rotateDoubleLeft x n (Tree av 2 al ar) (Tree y 0 (Tree z 1 b_1 b_2) (Tree cv 2 cl cr)) = Tree z n (Tree x 1 (Tree av 1 al ar) b_1) (Tree y 1 b_2 (Tree cv 1 cl cr)) 
rotateDoubleLeft x n (Tree av 2 al ar) (Tree y 0 (Tree z 1 b_1 b_2) (Nil 2))           = Tree z n (Tree x 1 (Tree av 1 al ar) b_1) (Tree y 1 b_2 (Nil 1)) 
rotateDoubleLeft x n (Nil 2) (Tree y 0 (Tree z 1 b_1 b_2) (Tree cv 2 cl cr))           = Tree z n (Tree x 1 (Nil 1) b_1) (Tree y 1 b_2 (Tree cv 1 cl cr)) 
rotateDoubleLeft x n (Nil 2) (Tree y 0 (Tree z 1 b_1 b_2) (Nil 2))                     = Tree z n (Tree x 1 (Nil 1) b_1) (Tree y 1 b_2 (Nil 1)) 
rotateDoubleLeft _ _ _ _ = error "Tree did not match criteria"

-- Test
main = do
    mapM_ print [a,b,c,d]
  where
    a = initialT 5
    b = insert 2 a
    c = insert 3 b
    d = insert 7 c

-- Liquid Haskell

{-@ die :: {v:String | false } -> a  @-}
die msg = error msg

{-@ predicate HtDiff S T D = (ht S) - (ht T) == D @-}
{-@ predicate EqHt S T = (ht S) == (ht T) @-}

{-@ predicate LeftHeavy T = bFac T == 1 @-}
{-@ predicate RightHeavy T = bFac T == -1 @-}

{-@ predicate EqRdSum S T = rdSum S == rdSum T @-}
{-@ predicate EqRd S T = rd S == rd T @-}
{-@ predicate RdDiff S T N = rd S - rd T = N @-}

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced (Nil _) = True
balanced (Tree _ n l r) = 0 <= n && n <= 2 
                       && rdSum l == rdSum r 
                       && (balanced' l)
                       && (balanced' r)

{-@ measure balanced' @-}
balanced' :: Tree a -> Bool
balanced' (Nil _) = True
balanced' (Tree _ n l r) = 1 <= n && n <= 2
                       && rdSum l == rdSum r 
                       && (balanced' l)
                       && (balanced' r)

-- my additions
{-@ type AlmostWavl = {t:Tree | (not (notEmptyTree t) || (balanced (left t) && balanced (right t))) } @-}


{-@ measure left :: NETree -> Tree @-}
left :: Tree a -> Tree a
left (Tree _ _ l _) = l
left (Nil _) = error "Nothing to return"

{-@ measure right :: NETree -> Tree @-}
right :: Tree a -> Tree a
right (Tree _ _ _ r) = r
right (Nil _) = error "Nothing to return"

-- get rankdiff
{-@ measure rd @-}
{-@ rd :: Tree a -> RankDiff @-}
rd :: Tree a -> Int
rd (Nil n) = n
rd (Tree _ n _ _) = n

{-@ measure rdSum @-}
rdSum :: Tree a -> Int
rdSum (Nil n) = n
rdSum (Tree _ n l r) = n + rdSum l + rdSum r 

{-@ type Wavl = {v: Tree a | balanced v} @-}