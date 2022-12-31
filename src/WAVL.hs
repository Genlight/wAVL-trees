{-@ LIQUID "--short-names" @-}

module WAVL (Tree, singleton
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
    GT -> insR
    EQ -> t
    where 
        l' = insert x l
        r' = insert x r
        lt' = Tree v n l' r
        rt' = Tree v n l r'
        insL | rk l' < n = lt'
             | rk l' == n && rk l' == rk r + 1 = promoteL lt'
             | rk l' == n && rk l' == rk r + 2 && (rk (left l') + 1) == rk l' && (rk (right l') + 2) == rk l' && notEmptyTree (left l') = rotateRight lt' 
             | rk l' == n && rk l' == rk r + 2 && (rk (right l') + 1) == rk l' && (rk (left l') + 2) == rk l' && notEmptyTree (right l') = rotateDoubleRight lt' 
             | otherwise = t
        insR | rk r' < n = rt'
             | rk r' == n && rk r' == rk l + 1 = promoteR rt'
             | rk r' == n && rk r' == rk l + 2 && (rk (left r') + 2) == rk r' && (rk (right r') + 1) == rk r' && notEmptyTree (right r') = rotateLeft rt'
             | rk r' == n && rk r' == rk l + 2 && (rk (left r') + 1) == rk r' && (rk (right r') + 2) == rk r' && notEmptyTree (left r') = rotateDoubleLeft rt'
             | otherwise = t

{-@ promoteL :: s:Node0_1 -> {t:Wavl | notEmptyTree t && (RkDiff t s 1)} @-}
promoteL :: Tree a -> Tree a
promoteL (Tree a n l r) = (Tree a (n+1) l r)

{-@ promoteR :: s:Node1_0 -> {t:Wavl | notEmptyTree t && (RkDiff t s 1)} @-}
promoteR :: Tree a -> Tree a
promoteR (Tree a n l r) = (Tree a (n+1) l r)

{-@ rotateRight :: {v:Node0_2 | notEmptyTree (left v) && notEmptyTree (left (left v)) && (rk (left v) == rk (right (left v)) + 2) } -> {t:Wavl | notEmptyTree t && EqRk v t } @-}
rotateRight :: Tree a -> Tree a
rotateRight (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)

{-@ rotateDoubleRight :: {v:Node0_2 | notEmptyTree (left v) && notEmptyTree (right (left v)) && IsNode2_1 (left v) } -> {t:Wavl | notEmptyTree t && EqRk v t } @-}
rotateDoubleRight :: Tree a -> Tree a
rotateDoubleRight (Tree z n (Tree x m a (Tree y o b c)) d) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 

{-@ rotateLeft :: {v:Node2_0 | notEmptyTree (right v) && (rk (right v) == rk (left (right v)) + 2) } -> {t:Wavl | notEmptyTree t && EqRk v t } @-}
rotateLeft :: Tree a -> Tree a
rotateLeft t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c

{-@ rotateDoubleLeft :: {v:Node2_0 | notEmptyTree (right v) && notEmptyTree (left (right v)) && IsNode1_2 (right v) } -> {t:Wavl | notEmptyTree t && EqRk v t } @-}
rotateDoubleLeft :: Tree a -> Tree a
rotateDoubleLeft t@(Tree x n a (Tree y m (Tree z o b_1 b_2) c)) =
  Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 

-- Liquid Haskell
{-@ predicate HtDiff S T D = (ht S) - (ht T) == D @-}
{-@ predicate EqHt S T = (ht S) == (ht T) @-}

-- predicates by me
{-@ predicate EqRk S T = rk T == rk S @-}
{-@ predicate RkDiff S T D = (rk S) - (rk T) == D @-}

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced Nil = True
balanced t@(Tree _ n l r) = rk r < n && n <= rk r + 2 
                         && rk l < n && n <= rk l + 2
                         && (balanced l)
                         && (balanced r)

-- my additions
{-@ measure rk @-}
{-@ rk :: Tree a -> Int @-}
rk :: Tree a -> Int
rk Nil =  -1
rk (Tree _ n _ _) = n

{-@ type Wavl = {v: Tree a | balanced v } @-}

-- {-@ type Rank = {v:Int | v >= -1} @-}
{-@ type Rank = Int @-}
{-@ type AlmostWavl = {t:Tree a | (not (notEmptyTree t)) || ((balanced (left t) && balanced (right t))) } @-}


{-@ type Node0_1 = { v:AlmostWavl | notEmptyTree v && (RkDiff v (left v) 0 ) && (RkDiff v (right v) 1) } @-}
{-@ type Node1_0 = { v:AlmostWavl | notEmptyTree v && (RkDiff v (left v) 1 ) && (RkDiff v (right v) 0) } @-}

{-@ type Node0_2 = { v:AlmostWavl | notEmptyTree v && (EqRk v (left v) && RkDiff v (right v) 2 ) } @-}
{-@ type Node2_0 = { v:AlmostWavl | notEmptyTree v && (RkDiff v (left v) 2 && EqRk v (right v) ) } @-}

{-@ type Node1_3 = { v:AlmostWavl | notEmptyTree v && RkDiff v (left v) 1 && RkDiff v (right v) 3 } @-}
{-@ type Node3_1 = { v:AlmostWavl | notEmptyTree v && RkDiff v (left v) 3 && RkDiff v (right v) 1 } @-}
{-@ type Node3_2 = { v:AlmostWavl | notEmptyTree v && RkDiff v (left v) 3 && RkDiff v (right v) 2 } @-}
{-@ type Node2_3 = { v:AlmostWavl | notEmptyTree v && RkDiff v (left v) 2 && RkDiff v (right v) 3 } @-}

{-@ predicate IsNode2_2 T = (rk (left T)) + 2 == (rk T) && (rk (right T)) + 2 == rk T @-}
{-@ predicate IsNode1_2 T = (rk (left T)) + 1 == (rk T) && (rk (right T)) + 2 == rk T @-}
{-@ predicate IsNode2_1 T = (rk (left T)) + 2 == (rk T) && (rk (right T)) + 1 == rk T @-}

{-@ measure isNode1_2 @-}
{-@ isNode1_2 :: {v:Tree a | notEmptyTree v} -> Bool @-}
isNode1_2 :: Tree a -> Bool
isNode1_2 (Tree _ n l r) = (n == 1 + rk l) && (n == 2 + rk r)

{-@ measure isNode2_1 @-}
{-@ isNode2_1 :: {v:Tree a | notEmptyTree v} -> Bool @-}
isNode2_1 :: Tree a -> Bool
isNode2_1 (Tree _ n l r) = (n == 2 + rk l) && (n == 1 + rk r)

{-@ idWavl :: {t:Wavl | notEmptyTree t} -> {s:Wavl | notEmptyTree s} @-}
idWavl :: Tree a -> Tree a
idWavl t = t

-- Deletion functions
-- {-@ delete :: (Ord a) => a -> s:Wavl -> {t:Wavl | (EqRk s t) || (RkDiff s t 1)} @-}
-- delete _ Nil = Nil
-- delete y (Tree x n l r)
--   | y < x     = balLDel x n l' r
--   | x < y     = balRDel x n l r'
--   | otherwise = merge y l r n 
--     where
--       l' = delete x l
--       r' = delete x r

{-@ predicate WavlRank T L R = rk R < rk T && rk T <= (rk R) + 2
                            && rk L < rk T && rk T <= (rk L) + 2 @-}

{-@ predicate WavlRankN N L R = rk R < N && N <= rk R + 2
                            && rk L < N && N <= rk L + 2 @-}
{-@ predicate WavlRankL N L R = rk R < N && N <= rk R + 2
                            && rk L < N && N <= rk L + 3 @-}
{-@ predicate WavlRankR N L R = rk R < N && N <= rk R + 3
                            && rk L < N && N <= rk L + 2 @-}

{-@ merge :: x:a -> l:Wavl -> r:Wavl -> {v:Rank | WavlRankN v l r }  -> t:Wavl @-}
merge :: a -> Tree a -> Tree a -> Int ->  Tree a
merge _ Nil Nil _ = Nil
merge _ Nil r _  = r
merge _ l Nil _  = l
merge x l r n    = (balRDel x l r n)
-- merge x l r n    = (balRDel y l r' n)
--   where
  --  (r', y)     = getMin r

-- get the inorder follow up node 
-- {-@  getMin :: {v:Wavl | notEmptyTree v} -> ({t:Wavl | (EqRk v t) || (RkDiff v t 1) }, a) @-} 
-- getMin :: Tree a -> (Tree a, a)
-- getMin (Tree x _ Nil r) = (r, x)
-- getMin (Tree x n l r)    = ((balLDel x l' r n), x')
--   where
--     (l', x')             = getMin l

{-@ balLDel :: a -> l:Wavl -> r:Wavl -> {n:Rank | WavlRankN n l r} -> t:Wavl  @-}
balLDel :: a -> Tree a -> Tree a -> Int -> Tree a
balLDel x Nil Nil 1  = singleton x
balLDel x Nil Nil 0  = singleton x 
balLDel x l r n  | n <= (rk l) + 2 = t 
                | n == (rk l) + 3 && (rk r) + 2 == n = demoteL t 
                | n == (rk l) + 3 && (rk r) + 1 == n && (notEmptyTree r) && (rk (left r)) + 2 == (rk r) && (rk (right r)) + 2 == rk r = doubleDemoteL t
                | n == (rk l) + 3 && (rk r) + 1 == n && notEmptyTree r && (rk (right r) + 1) == rk r = rotateLeftD t
                | n == (rk l) + 3 && (rk r) + 1 == n && notEmptyTree r && (rk (right r) + 2) == rk r && (rk (left r)) + 1 == rk r = doubleRotateLeftD t
                | otherwise = t
                  where
                    t = Tree x n l r

{-@ balRDel :: a -> l:Wavl -> r:Wavl -> {n:Rank | WavlRankN n l r} -> t:Wavl @-}
balRDel :: a -> Tree a -> Tree a -> Int -> Tree a
balRDel x Nil Nil 1  = singleton x
balRDel x Nil Nil 0  = singleton x
balRDel x l r n | n < (rk r + 3) = t
                | n == (rk r + 3) && (rk l) + 2 == n = demoteR t
                | n == (rk r + 3) && (rk l) + 1 == n && notEmptyTree l && (rk (left l)) + 2 == rk l && (rk (right l)) + 2 == rk l = doubleDemoteR t
                | n == (rk r + 3) && (rk l) + 1 == n && notEmptyTree l && (rk (left l)) + 1 == rk l = rotateRightD t   
                | n == (rk r + 3) && (rk l) + 1 == n && notEmptyTree l  && notEmptyTree (right l) && (rk (left l)) + 2 == rk l && (rk (right l)) + 1 == rk l = rotateDoubleRightD t   
                | otherwise = t
                    where 
                      t = (Tree x n l r)

{-@ predicate RankChild S N = rk S < N && (rk S) + 2 >= N @-}

{-@ demoteL :: s:Node3_2 -> {t:Wavl | RkDiff s t 1} @-}
demoteL :: Tree a -> Tree a
demoteL (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteL :: {s:Node3_1 | notEmptyTree (right s) && IsNode2_2 (right s) } -> {t:Wavl | RkDiff s t 1 } @-}
doubleDemoteL :: Tree a -> Tree a
doubleDemoteL (Tree x n l (Tree y m rl rr)) = (Tree x (n-1) l (Tree x (m-1) rl rr))

{-@ rotateLeftD :: {s:Node3_1 | notEmptyTree (right s) && (rk (right (right s))) + 1 == rk (right s) } -> {t:Wavl | EqRk s t} @-}
rotateLeftD :: Tree a -> Tree a
rotateLeftD t@(Tree z n Nil (Tree y m Nil w)) = Tree y (m+1) (Tree z (n-2) Nil Nil) w 
rotateLeftD t@(Tree z n x (Tree y m v w)) = Tree y (m+1) (Tree z (n-1) x v) w 

{-@ doubleRotateLeftD :: {s:Node3_1 | notEmptyTree (right s) && notEmptyTree (left (right s)) && IsNode1_2 (right s) } -> {t:Wavl | EqRk s t} @-}
doubleRotateLeftD :: Tree a -> Tree a
doubleRotateLeftD t@(Tree z n x (Tree y m (Tree v o vl vr) yr)) = Tree v (o+2) (Tree z (n-2) x vl) (Tree y (m-1) vr yr)

{-@ demoteR :: s:Node2_3 -> {t:Wavl | RkDiff s t 1} @-}
demoteR :: Tree a -> Tree a
demoteR (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteR :: {s:Node1_3 | notEmptyTree (left s) && IsNode2_2 (left s) } -> {t:Wavl | RkDiff s t 1 } @-}
doubleDemoteR :: Tree a -> Tree a
doubleDemoteR (Tree x n (Tree y m ll lr) r) = Tree x (n-1) (Tree y (m-1) ll lr) r 

{-@ rotateRightD :: {s:Node1_3 | notEmptyTree (left s) && rk(left (left s)) +1 = rk (left s) } -> {t:Wavl | EqRk s t} @-}
rotateRightD :: Tree a -> Tree a
rotateRightD (Tree x n (Tree y m ll Nil) Nil) = Tree y (m+1) ll (Tree x (n-2) Nil Nil) 
rotateRightD (Tree x n (Tree y m ll lr) r) = Tree y (m+1) ll (Tree x (n-1) lr r) 

{-@ rotateDoubleRightD :: {s:Node1_3 | notEmptyTree (left s) && notEmptyTree (right (left s)) && IsNode2_1 (left s) } -> {t:Wavl | EqRk s t} @-}
rotateDoubleRightD :: Tree a -> Tree a
rotateDoubleRightD (Tree x n (Tree y m ll (Tree z o lrl lrr)) r) = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)

-- Test
main = do
    mapM_ print [a,b,c,d]
  where
    a = singleton 5
    b = insert 2 a
    c = insert 3 b
    d = insert 7 c