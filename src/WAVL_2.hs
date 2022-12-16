{-@ LIQUID "--counter-examples" @-}
{-@ LIQUID "--short-names" @-}

module WAVL_2 (Tree, singleton
--  insert,
 ) where

-- Basic functions
{-@ data Tree [ht] @-} 
data Tree a = Nil | Tree a Int (Tree a) (Tree a) deriving Show

{-@ measure left @-}
{-@ left :: {v: Tree a | notEmptyTree v} -> Tree a @-}
left :: Tree a -> Tree a
left (Tree x n l r) = l

{-@ measure right @-}
{-@ right :: {v: Tree a | notEmptyTree v} -> Tree a @-}
right :: Tree a -> Tree a
right (Tree x n l r) = r

{-@ val :: {v: Tree a | notEmptyTree v} -> a @-}
val :: Tree a -> a
val (Tree a n l r) = a 

{-@ measure notEmptyTree @-}
notEmptyTree :: Tree a -> Bool
notEmptyTree Nil = False
notEmptyTree _ = True

{-@ measure ht @-}
{-@ ht :: Tree a -> Nat @-}
ht              :: Tree a -> Int
ht Nil          = 0
ht (Tree x n l r) = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

{-@ htDiff :: s:Tree a -> t: Tree a -> {v: Int | HtDiff s t v} @-}
htDiff :: Tree a -> Tree a -> Int
htDiff l r = ht l - ht r

{-@ emp :: {v: Wavl | ht v == 0 && rk v == (-1) } @-}
emp = Nil

{-@ singleton :: a -> {v: Wavl | notEmptyTree v && rk v == 0 && ht v == 1 }@-}
singleton a = Tree a 0 Nil Nil

-- insertion
{-@ insert :: (Ord a) => a -> s:Wavl -> {t:Wavl | notEmptyTree t && ((RkDiff t s 1) || (RkDiff t s 0)) } @-}
insert :: (Ord a) => a -> Tree a -> Tree a
insert x Nil = singleton x
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> t
    EQ -> t
    where 
        l' = insert x l
        lt' = Tree v n l' r
        insL | rk l' < n = lt'
             | rk l' == rk r + 1 = promoteL lt' -- rk l' == n
             | (rk (right l') + 2) == rk l' = rotateRight lt' -- rk l' == rk r + 2
            --  | (rk (right l') + 1) == rk l' = rotateDoubleRight lt' -- rk l' == rk r + 2
             | otherwise = t

{-@ promoteL :: s:Node0_1 -> {t:Wavl | notEmptyTree t && (RkDiff t s 1)} @-}
promoteL :: Tree a -> Tree a
promoteL (Tree a n l r) = (Tree a (n+1) l r)

{-@ rotateRight :: {v:Node0_2 | notEmptyTree (left v) && (rk (left v) == rk (right (left v)) + 2) && (rk (left v) == rk (right (left v)) + 2) } -> {t:Wavl | notEmptyTree t && EqRk v t } @-}
-- promote Nil = die "NIL cannot be promoted"
rotateRight :: Tree a -> Tree a
rotateRight (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)

{-@ rotateDoubleRight :: {v:Node0_2 | notEmptyTree (left v) && notEmptyTree (right (left v)) && (rk (left v) == rk (right (left v)) + 1) 
                                                                                             && (rk (left v) == rk (left (left v)) + 2) } -> {t:Wavl | notEmptyTree t && EqRk v t } @-}
rotateDoubleRight :: Tree a -> Tree a
rotateDoubleRight (Tree z n (Tree x m a (Tree y o b c)) d) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 




-- Liquid Haskell
{-@ predicate HtDiff S T D = (ht S) - (ht T) == D @-}
{-@ predicate EqHt S T = (ht S) == (ht T) @-}

-- predicates by me
{-@ predicate EqRk S T = rk T == rk S @-}
{-@ predicate RkDiff S T D = (rk S) - (rk T) == D @-}

-- {-@ measure rkDiff @-}
-- rkDiff :: Int -> Tree a -> Int -> Bool
-- rkDiff n s d = n - (rk s) == d

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced Nil = True
balanced t@(Tree _ n l r) = 
    rk r < n && n <= rk r + 2 && 
    rk l < n && n <= rk l + 2
                      --  && not2_2Node n l r -- this term is only allowed with insertion only trees
                       && (balanced l)
                       && (balanced r)

-- my additions

{-@ measure rk @-}
{-@ rk :: Tree a -> Int @-}
rk :: Tree a -> Int
rk Nil =  -1
rk (Tree _ n _ _) = n

{-@ type Wavl = {v: Tree a | balanced v} @-}

{-@ type AlmostWavl = {t:Tree a | (not (notEmptyTree t)) || ((balanced (left t) && balanced (right t))) } @-}

{-@ type Node0_1 = { v:AlmostWavl | notEmptyTree v && (RkDiff v (left v) 0 ) && (RkDiff v (right v) 1)
                                                      } @-}
{-@ type Node0_2 = { v:AlmostWavl | notEmptyTree v && (EqRk v (left v) && RkDiff v (right v) 2 ) } @-}

{-@ measure isNode1_2 @-}
{-@ isNode1_2 :: {v:Tree a | notEmptyTree v} -> Bool @-}
isNode1_2 :: Tree a -> Bool
isNode1_2 (Tree _ n l r) = (n == 1 + rk l) && (n == 2 + rk r)

{-@ idWavl :: Wavl -> Wavl @-}
idWavl :: Tree a -> Tree a
idWavl t = t

-- Test
main = do
    idWavl v
    where 
        v = Tree 4 2 (Tree 1 1 (Tree 0 0 Nil Nil) Nil) (Tree 5 0 Nil Nil)   
