{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--exact-data-cons" @-}
-- {-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--counter-examples" @-}

module WAVL (Tree, singleton,
 insert,
 ) where

-- Basic functions
{-@ data Tree [ht] a = Nil {rd' :: {v:Int | v == -1}} | Tree { val :: a, 
                                    rd :: {v:Int | v >= 0}, 
                                    left :: Tree a,
                                    right :: Tree a } @-} 
data Tree a = Nil {rd' :: Int} | Tree { val :: a, rd :: Int, left :: (Tree a), right :: (Tree a)} deriving Show

{-@ type Wavl = {v: Tree a | balanced v } @-}
{-@ type NEWavl = {v:Wavl | notEmptyTree v && rk v >= 0 } @-}

{-@ type AlmostWavl = {t:Tree a | (not (notEmptyTree t)) || (balanced (left t) && balanced (right t)) } @-}
{-@ type Rank = {v:Int | v >= -1} @-}

{-@ measure rk @-}
{-@ rk :: Tree a -> Int @-}
rk :: Tree a -> Int
rk (Nil (-1)) =  -1
rk t@(Tree _ n _ _) = rd t -- n -- exchange to "rd t" leads to endless errors ?!

nil :: Tree a
nil = Nil (-1)

{-@ measure notEmptyTree @-}
notEmptyTree :: Tree a -> Bool
notEmptyTree (Nil _) = False
notEmptyTree _ = True

{-@ measure ht @-}
{-@ ht :: Tree a -> Rank @-}
ht              :: Tree a -> Int
ht (Nil _)          = (-1)
ht (Tree x n l r) = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

{-@ htDiff :: s:Tree a -> t: Tree a -> {v: Int | HtDiff s t v} @-}
htDiff :: Tree a -> Tree a -> Int
htDiff l r = ht l - ht r

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced (Nil _) = True
balanced t@(Tree _ n l r) = rk r < n && n <= rk r + 2 
                         && rk l < n && n <= rk l + 2
                         && ((notEmptyTree l) || (notEmptyTree r) || (n == 0)) -- disallow 2,2-leafs
                         && (balanced l)
                         && (balanced r)

-- {-@ measure heightass @-}
-- heightass :: Tree a -> Bool
-- heightass t@Nil = True
-- heightass t@(Tree _ _ l r) = rk t <= 2 * (ht t) && ht t <= rk t && heightass l && heightass r  

-- {-@ inline EmpEqRk0 @-}
-- EmpEqRk0 :: Tree a -> Bool
-- EmpEqRk0 t = 


{-@ emp :: {v:Wavl | ht v == (-1) && rk v == (-1) } @-}
emp = nil

{-@ singleton :: a -> {v:NEWavl | ht v == 0 && rk v == 0 }@-}
singleton a = Tree a 0 nil nil

-- insertion
{-@ insert :: (Ord a) => a -> s:Wavl -> {t:NEWavl | ((RkDiff t s 1) || (RkDiff t s 0)) } @-}
insert :: (Ord a) => a -> Tree a -> Tree a
insert x (Nil _) = singleton x
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
             | rk l' == n && rk l' == rk r + 2 && (rk (left l') + 1) == rk l' && (rk (right l') + 2) == rk l' && notEmptyTree (left l') && isEqEmp r (right l') = rotateRight lt' 
             | rk l' == n && rk l' == rk r + 2 && (rk (right l') + 1) == rk l' && (rk (left l') + 2) == rk l' && notEmptyTree (right l') && isEqEmp r (left l') = rotateDoubleRight lt' 
             | otherwise = t
        insR | rk r' < n = rt'
             | rk r' == n && rk r' == rk l + 1 = promoteR rt'
             | rk r' == n && rk r' == rk l + 2 && (rk (left r') + 2) == rk r' && (rk (right r') + 1) == rk r' && notEmptyTree (right r') && isEqEmp l (left r') && n >= 1 = rotateLeft rt'
             | rk r' == n && rk r' == rk l + 2 && (rk (left r') + 1) == rk r' && (rk (right r') + 2) == rk r' && notEmptyTree (left r') && isEqEmp l (right r') && n >= 1 = rotateDoubleLeft rt'
             | otherwise = t

{-@ promoteL :: s:Node0_1 -> {t:NEWavl | RkDiff t s 1} @-}
promoteL :: Tree a -> Tree a
promoteL (Tree a n l r) = (Tree a (n+1) l r)

{-@ promoteR :: s:Node1_0 -> {t:NEWavl | RkDiff t s 1} @-}
promoteR :: Tree a -> Tree a
promoteR (Tree a n l r) = (Tree a (n+1) l r)

{-@ rotateRight :: {v:Node0_2 | notEmptyTree (left (left v)) && IsNode1_2 (left v) && EqEmp (right (left v)) (right v) } -> {t:NEWavl | EqRk v t } @-}
rotateRight :: Tree a -> Tree a
rotateRight (Tree x n (Tree y m a b) c@nil) = Tree y m a (Tree x (n-1) b c)
rotateRight (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)

{-@ rotateDoubleRight :: {v:Node0_2 | notEmptyTree (right (left v)) && IsNode2_1 (left v) && EqEmp (right v) (left (left v))} -> {t:NEWavl | EqRk v t } @-}
rotateDoubleRight :: Tree a -> Tree a
rotateDoubleRight (Tree z n (Tree x m a (Tree y o b c)) d@nil) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 
rotateDoubleRight (Tree z n (Tree x m a (Tree y o b c)) d) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 

{-@ rotateLeft :: {v:Node2_0 | notEmptyTree (right v) && notEmptyTree (right (right v)) && IsNode2_1 (right v) && EqEmp (left v) (left (right v))} -> {t:NEWavl | EqRk v t } @-}
rotateLeft :: Tree a -> Tree a
rotateLeft t@(Tree x n a@nil (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c
rotateLeft t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c

{-@ rotateDoubleLeft :: {v:Node2_0 | notEmptyTree (left (right v)) && IsNode1_2 (right v) && EqEmp (left v) (right (right v))} -> {t:NEWavl | EqRk v t } @-}
rotateDoubleLeft :: Tree a -> Tree a
rotateDoubleLeft (Tree x n a@nil (Tree y m (Tree z o b_1 b_2) c)) = Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 
rotateDoubleLeft (Tree x n a (Tree y m (Tree z o b_1 b_2) c)) = Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 

-- Liquid Haskell
{-@ predicate HtDiff S T D = (ht S) - (ht T) == D @-}
{-@ predicate EqHt S T = (ht S) == (ht T) @-}

-- predicates by me
{-@ predicate EqRk S T = rk T == rk S @-}
{-@ predicate RkDiff S T D = (rk S) - (rk T) == D @-}

{-@ predicate EqRkN N T = rk T == N @-}
{-@ predicate RkDiffN N T D = N - (rk T) == D @-}

-- Could be even more be specified by cutting down 
-- {-@ type AlmostWavlD = {t:AlmostWavl | (not (notEmptyTree t)) || (Is3Child t (left t) && Is3Child t (right t))} @-}

{-@ type Node0_1 = { v:AlmostWavl | notEmptyTree v  && notEmptyTree (left v) && (RkDiff v (left v) 0 ) && (RkDiff v (right v) 1) && rk v >= 0 } @-}
{-@ type Node1_0 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && (RkDiff v (left v) 1 ) && (RkDiff v (right v) 0) && rk v >= 0 } @-}

{-@ type Node0_2 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v) && EqRk v (left v) && RkDiff v (right v) 2  && rk v >= 1 } @-}
{-@ type Node2_0 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && EqRk v (right v) && RkDiff v (left v) 2 && rk v >= 1 } @-}

{-@ type Node1_3 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v) && RkDiff v (left v) 1 && RkDiff v (right v) 3  && rk v >= 2 } @-}
{-@ type Node3_1 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && RkDiff v (left v) 3 && RkDiff v (right v) 1 && rk v >= 2 } @-}
{-@ type Node3_2 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && RkDiff v (left v) 3 && RkDiff v (right v) 2 && rk v >= 2 } @-}
{-@ type Node2_3 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v) && RkDiff v (left v) 2 && RkDiff v (right v) 3  && rk v >= 2 } @-}

{-@ predicate IsNode2_2 T = (rk (left T)) + 2 == (rk T) && (rk (right T)) + 2 == rk T @-}
{-@ predicate IsNode1_2 T = (rk (left T)) + 1 == (rk T) && (rk (right T)) + 2 == rk T @-}
{-@ predicate IsNode2_1 T = (rk (left T)) + 2 == (rk T) && (rk (right T)) + 1 == rk T @-}

{-@ predicate Is3Child T S = (rk S) + 3 >= (rk T) && (rk T) > (rk S) @-}
{-@ predicate Is2Child T S = (rk S) + 2 >= (rk T) && (rk T) > (rk S) @-}

{-@ predicate WavlRank T L R = rk R < rk T && rk T <= (rk R) + 2
                            && rk L < rk T && rk T <= (rk L) + 2 @-}

{-@ predicate WavlRankN N L R = rk R < N && N <= rk R + 2
                            && rk L < N && N <= rk L + 2 @-}
{-@ predicate WavlRankL N L R = rk R < N && N <= rk R + 2
                            && rk L < N && N <= rk L + 3 @-}
{-@ predicate WavlRankR N L R = rk R < N && N <= rk R + 3
                            && rk L < N && N <= rk L + 2 @-}

{-@ predicate Child3 N T = rk T + 3 == N @-}
{-@ predicate Child2 N T = rk T + 2 == N @-}
{-@ predicate Child1 N T = rk T + 1 == N @-}

{-@ predicate EqEmp S T = (not (notEmptyTree S) || (notEmptyTree T) )
                              && ((notEmptyTree S) || not (notEmptyTree T) ) @-}

{-@ inline isEqEmp @-}
isEqEmp :: Tree a -> Tree a -> Bool
isEqEmp s t = ((not (notEmptyTree s) || (notEmptyTree t) ) && ((notEmptyTree s) || not (notEmptyTree t)))
-- isEqEmp s t = (notEmptyTree s) <=> (notEmptyTree t)

-- {-@ measure isNode1_2 @-}
-- {-@ isNode1_2 :: {v:Tree a | notEmptyTree v} -> Bool @-}
-- isNode1_2 :: Tree a -> Bool
-- isNode1_2 (Tree _ n l r) = (n == 1 + rk l) && (n == 2 + rk r)

-- {-@ measure isNode2_1 @-}
-- {-@ isNode2_1 :: {v:Tree a | notEmptyTree v} -> Bool @-}
-- isNode2_1 :: Tree a -> Bool
-- isNode2_1 (Tree _ n l r) = (n == 2 + rk l) && (n == 1 + rk r)

{-@ idWavl :: t:NEWavl -> s:NEWavl @-}
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

-- {-@ merge :: x:a -> l:Wavl -> r:Wavl -> {v:Rank | WavlRankN v l r }  -> t:Wavl @-}
-- merge :: a -> Tree a -> Tree a -> Int ->  Tree a
-- merge _ Nil Nil _ = Nil
-- merge _ Nil r _  = r
-- merge _ l Nil _  = l
-- merge x l r n    = (balRDel y n l r')
--   where
--    (r', y)     = getMin r

-- get the inorder successor node 
-- {-@  getMin :: {v:Wavl | notEmptyTree v} -> ({t:Wavl | (EqRk v t) || (RkDiff v t 1) }, a) @-} 
-- getMin :: Tree a -> (Tree a, a)
-- getMin (Tree x _ Nil r) = (r, x)
-- getMin (Tree x n l r)    = ((balLDel x n l' r), x')
--   where
--     (l', x')             = getMin l

-- {-@ balLDel :: a -> n:Rank -> {l:Wavl | rk l + 3 >= n && rk l < n} -> {r:Wavl | rk r + 2 >= n && n > rk r} -> {t:Wavl | (rk t == n || rk t + 1 == n) && notEmptyTree t }  @-}
-- balLDel :: a -> Int -> Tree a -> Tree a -> Tree a
-- balLDel x 0 Nil Nil  = singleton x
-- balLDel x 1 Nil Nil  = singleton x
-- balLDel x n l r | n <= (rk l) + 2 = t 
--                 | n == (rk l) + 3 && (rk r) + 2 == n && notEmptyTree r  = demoteL t 
--                 | n == (rk l) + 3 && notEmptyTree r && (rk r) + 1 == n = doMoreBalL x n l r
--                 | otherwise = t
--                   where
--                     t = Tree x n l r
                
-- {-@ doMoreBalL :: a -> n:Rank -> {l:Wavl | Child3 n l} -> {r:Wavl | notEmptyTree r && Child1 n r} -> {t:Wavl | (rk t == n || rk t + 1 == n) && notEmptyTree t } @-}
-- doMoreBalL x n l r 
--   | notEmptyTree (left r)  && notEmptyTree (right r) && rk (left r) + 2 == (rk r) && (rk (right r)) + 2 == rk r = doubleDemoteL (Tree x n l r)
--   | notEmptyTree (right r) && rk (right r) + 1 == rk r = rotateLeftD (Tree x n l r)
--   | notEmptyTree (left r)  && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = rotateDoubleLeftD (Tree x n l r)
--   | otherwise = (Tree x n l r)
  --   where 
  --     t = Tree x n l r

-- {-@ doMoreBalR :: a -> n:Rank -> {l:Wavl | Child1 n l && notEmptyTree l} -> {r:Wavl | Child3 n r} -> {t:Wavl | (rk t == n || rk t + 1 == n) && notEmptyTree t } @-}
-- {-@ doMoreBalR :: v:Node1_3 -> {t:NEWavl | (EqRk v t || RkDiff v t 1) } @-} 
-- doMoreBalR t@(Tree x n l r)                 
--   | notEmptyTree (left l) && notEmptyTree (right l) && (rk (left l)) + 2 == rk l && (rk (right l)) + 2 == rk l = doubleDemoteR t
--   -- | notEmptyTree (left l) && (rk (left l)) + 1 == rk l = rotateRightD t   
--   | notEmptyTree (left l) && (rk (left l)) + 1 == rk l = rotateRightD t   
--   | notEmptyTree (right l) && (rk (left l)) + 2 == rk l && (rk (right l)) + 1 == rk l && isEqEmp r (left l) = rotateDoubleRightD t
-- doMoreBalR t = t

-- {-@ balRDel :: a -> n:Rank -> {l:Wavl | rk l + 2 >= n && rk l < n} -> {r:Wavl | rk r + 3 >= n && rk r < n} -> {t:Wavl | (rk t == n || rk t + 1 == n) && notEmptyTree t } @-}
-- balRDel :: a -> Int -> Tree a -> Tree a -> Tree a
-- balRDel x 0 Nil Nil = singleton x
-- balRDel x 1 Nil Nil = singleton x
-- -- balRDel x n l Nil | 
-- balRDel x n l r | n < (rk r + 3) = t
--                 | n == (rk r + 3) && (rk l) + 2 == n && notEmptyTree l = demoteR t
--                 | n == (rk r + 3) && (rk l) + 1 == n && notEmptyTree l = doMoreBalR x n l r
--                 | otherwise = t
--                     where 
--                       t = Tree x n l r

{-@ demoteL :: s:Node3_2 -> {t:NEWavl | RkDiff s t 1 } @-}
demoteL :: Tree a -> Tree a
demoteL (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteL :: {s:Node3_1 | IsNode2_2 (right s) && notEmptyTree (left (right s)) && notEmptyTree (right (right s))} -> {t:NEWavl | RkDiff s t 1} @-}
doubleDemoteL :: Tree a -> Tree a
doubleDemoteL (Tree x n l (Tree y m rl rr)) = (Tree x (n-1) l (Tree x (m-1) rl rr))

{-@ rotateLeftD :: {s:Node3_1 | Child1 (rk (right s)) (right (right s)) } -> {t:NEWavl | EqRk s t } @-}
rotateLeftD :: Tree a -> Tree a
rotateLeftD t@(Tree z n zl@(Nil (-1)) (Tree y m yl@(Nil (-1)) w)) = Tree y (m+1) (singleton z) w 
rotateLeftD t@(Tree z n x (Tree y m v w)) = Tree y (m+1) (Tree z (n-1) x v) w 

{-@ rotateDoubleLeftD :: {s:Node3_1 | notEmptyTree (left (right s)) && IsNode1_2 (right s) && EqEmp (left s) (right (right s)) } 
                              -> {t:NEWavl | EqRk s t} @-}
rotateDoubleLeftD :: Tree a -> Tree a
rotateDoubleLeftD (Tree z n x (Tree y m (Tree v o vl vr) yr@nil)) = Tree v n (Tree z (n-2) x vl) (Tree y (n-2) vr yr)
rotateDoubleLeftD (Tree z n x (Tree y m (Tree v o vl vr) yr))     = Tree v n (Tree z (n-2) x vl) (Tree y (n-2) vr yr)

{-@ demoteR :: s:Node2_3 -> {t:NEWavl | RkDiff s t 1 } @-}
demoteR :: Tree a -> Tree a
demoteR (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteR :: {s:Node1_3 | IsNode2_2 (left s) && notEmptyTree (left (left s)) && notEmptyTree (right (left s)) } -> {t:NEWavl | RkDiff s t 1 } @-}
doubleDemoteR :: Tree a -> Tree a
doubleDemoteR (Tree x n (Tree y m ll lr) r) = Tree x (n-1) (Tree y (m-1) ll lr) r 

{-@ rotateRightD :: {s:Node1_3 | rk(left (left s)) +1 = rk (left s) } -> {t:NEWavl | EqRk s t } @-}
rotateRightD :: Tree a -> Tree a
rotateRightD (Tree x n (Tree y m ll (Nil (-1))) (Nil _)) = Tree y (m+1) ll (Tree x (n-2) nil nil) 
rotateRightD (Tree x n (Tree y m ll lr) r) = Tree y (m+1) ll (Tree x (n-1) lr r) 

{-@ rotateDoubleRightD :: {s:Node1_3 | notEmptyTree (right (left s)) && IsNode2_1 (left s) && EqEmp (right s) (left (left s))} -> {t:NEWavl | EqRk s t } @-}
rotateDoubleRightD :: Tree a -> Tree a
rotateDoubleRightD (Tree x n (Tree y m ll (Tree z o lrl lrr)) r@(Nil _)) = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)
rotateDoubleRightD (Tree x n (Tree y m ll (Tree z o lrl lrr)) r)     = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)

-- Test
main = do
    mapM_ print [a,b,c,d]
  where
    a = singleton 5
    b = insert 2 a
    c = insert 3 b
    d = insert 7 c