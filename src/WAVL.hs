{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--linear" @-}

module WAVL (Tree, singleton,
 insert, delete
 ) where

-- Basic functions
{-@ data Tree [ht] a = Nil {rd' :: {v:Int | v == (-1)}} | Tree { val :: a, 
                                    rd :: {v:Int | v >= 0 }, 
                                    left :: Tree a,
                                    right :: Tree a } @-} 
data Tree a = Nil {rd' :: Int} | Tree { val :: a, rd :: Int, left :: (Tree a), right :: (Tree a)} deriving Show

{-@ type Wavl = {v: Tree a | balanced v } @-} -- && ((not (notEmptyTree v)) || IsWavlNode v)
{-@ type NEWavl = {v:Wavl | notEmptyTree v && rk v >= 0 && IsWavlNode v } @-}

{-@ type AlmostWavl = {t:Tree a | (not (notEmptyTree t)) || (balanced (left t) && balanced (right t)) } @-}
{-@ type Rank = {v:Int | v >= -1} @-}

{-@ measure rk @-}
{-@ rk :: t:Tree a -> {v:Rank | (not (notEmptyTree t) || v >= 0) && (notEmptyTree t || v== (-1))} @-}
rk :: Tree a -> Int
rk (Nil _) =  -1
rk t@(Tree _ n _ _) = n

{-@ nil :: {v:Wavl | rk v == (-1) && not (notEmptyTree v) && ht v == (-1)} @-}
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
                        --  && isWavlNode t -- last point 
                         && (balanced l)
                         && (balanced r)

-- alternative balance definition
-- {-@ measure balanced' @-}
-- balanced' :: Tree a -> Bool
-- balanced' (Nil _) = True
-- balanced' t@(Tree _ n l r) = isWavlNode t
--   && (balanced' l)
--   && (balanced' r)

{-@ measure isWavlNode @-}  
isWavlNode :: Tree a -> Bool
isWavlNode (Nil _) = True 
isWavlNode t@(Tree x n l r) =  ((rk l) + 2 == n && (rk r) + 2 == n && notEmptyTree l && notEmptyTree r) ||
                ((rk l) + 1 == n && (rk r) + 2 == n) ||
                ((rk l) + 2 == n && (rk r) + 1 == n) ||
                ((rk l) + 1 == n && (rk r) + 1 == n)
  
-- {-@ measure heightass @-}
-- heightass :: Tree a -> Bool
-- heightass t@Nil = True
-- heightass t@(Tree _ _ l r) = rk t <= 2 * (ht t) && ht t <= rk t && heightass l && heightass r  

{-@ singleton :: a -> {v:NEWavl | ht v == 0 && rd v == 0 && rk v == rd v && isWavlNode v} @-}
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

{-@ promoteL :: s:Node0_1 -> {t:Node1_2 | RkDiff t s 1 && isWavlNode t } @-}
promoteL :: Tree a -> Tree a
promoteL (Tree a n l r) = (Tree a (n+1) l r)

{-@ promoteR :: s:Node1_0 -> {t:NEWavl | RkDiff t s 1} @-}
promoteR :: Tree a -> Tree a
promoteR (Tree a n l r) = (Tree a (n+1) l r)

{-@ rotateRight :: {v:Node0_2 | notEmptyTree (left (left v)) && IsNode1_2 (left v) && EqEmp (right (left v)) (right v) } -> {t:NEWavl | EqRk v t } @-}
rotateRight :: Tree a -> Tree a
rotateRight (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)

{-@ rotateDoubleRight :: {v:Node0_2 | notEmptyTree (right (left v)) && IsNode2_1 (left v) && EqEmp (right v) (left (left v))} -> {t:NEWavl | EqRk v t } @-}
rotateDoubleRight :: Tree a -> Tree a 
rotateDoubleRight (Tree z n (Tree x m a (Tree y o b c)) d) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 

{-@ rotateLeft :: {v:Node2_0 | notEmptyTree (right v) && notEmptyTree (right (right v)) && IsNode2_1 (right v) && EqEmp (left v) (left (right v))} -> {t:NEWavl | EqRk v t } @-}
rotateLeft :: Tree a -> Tree a
rotateLeft t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c

{-@ rotateDoubleLeft :: {v:Node2_0 | notEmptyTree (left (right v)) && IsNode1_2 (right v) && EqEmp (left v) (right (right v))} -> {t:NEWavl | EqRk v t } @-}
rotateDoubleLeft :: Tree a -> Tree a
rotateDoubleLeft (Tree x n a (Tree y m (Tree z o b_1 b_2) c)) = Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 

-- Liquid Haskell
{-@ predicate HtDiff S T D = (ht S) - (ht T) == D @-}
{-@ predicate EqHt S T = (ht S) == (ht T) @-}

-- predicates by me
{-@ predicate EqRk S T = rk T == rk S @-}
{-@ predicate RkDiff S T D = (rk S) - (rk T) == D @-}

{-@ predicate EqRkN N T = rk T == N @-}
{-@ predicate RkDiffN N T D = N - (rk T) == D @-}

{-@ type Node0_1 = { v:AlmostWavl | notEmptyTree v  && notEmptyTree (left v) && (RkDiff v (left v) 0 ) && (RkDiff v (right v) 1) && rk v >= 0 } @-}
{-@ type Node1_0 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && (RkDiff v (left v) 1 ) && (RkDiff v (right v) 0) && rk v >= 0 } @-}

{-@ type Node2_1 = { v:NEWavl | notEmptyTree (right v) && (RkDiff v (left v) 2 ) && (RkDiff v (right v) 1) && rk v >= 0 } @-}
{-@ type Node1_2 = { v:NEWavl | notEmptyTree (left v) && IsNode1_2 v && rk v >= 0 } @-}

{-@ type Node0_2 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v) && EqRk v (left v) && RkDiff v (right v) 2  && rk v >= 1 } @-}
{-@ type Node2_0 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && EqRk v (right v) && RkDiff v (left v) 2 && rk v >= 1 } @-}

{-@ type Node1_3 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v) && RkDiff v (left v) 1 && RkDiff v (right v) 3  && rk v >= 2 } @-}
{-@ type Node3_1 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && RkDiff v (left v) 3 && RkDiff v (right v) 1 && rk v >= 2 } @-}
{-@ type Node3_2 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && RkDiff v (left v) 3 && RkDiff v (right v) 2 && rk v >= 2 } @-}
{-@ type Node2_3 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v) && RkDiff v (left v) 2 && RkDiff v (right v) 3  && rk v >= 2 } @-}

{-@ predicate IsNode2_2 T = (rk (left T)) + 2 == (rk T) && (rk (right T)) + 2 == rk T && notEmptyTree (left T) && notEmptyTree (right T) @-}
{-@ predicate IsNode1_2 T = (rk (left T)) + 1 == (rk T) && (rk (right T)) + 2 == rk T @-}
{-@ predicate IsNode2_1 T = (rk (left T)) + 2 == (rk T) && (rk (right T)) + 1 == rk T @-}
{-@ predicate IsNode1_1 T = (rk (left T)) + 1 == (rk T) && (rk (right T)) + 1 == rk T @-}

{-@ predicate IsWavlNode T = (IsNode1_2 T || IsNode2_1 T || IsNode2_2 T || IsNode1_1 T) @-}
{-@ type MaybeWavlNode = {v:Wavl | (not (notEmptyTree v) || IsWavlNode v) } @-}

{-@ predicate Is3Child T S = (rk S) + 3 >= (rk T) && (rk T) > (rk S) @-}
{-@ predicate Is2Child T S = (rk S) + 2 >= (rk T) && (rk T) > (rk S) @-}
{-@ predicate Is1Child T S = (rk S) + 1 >= (rk T) && (rk T) > (rk S) @-}

{-@ predicate Is3ChildN N S = (rk S) + 3 >= N && N > (rk S) @-}
{-@ predicate Is2ChildN N S = (rk S) + 2 >= N && N > (rk S) @-}
{-@ predicate Is1ChildN N S = (rk S) + 1 >= N && N > (rk S) @-}

{-@ predicate WavlRank T L R = rk R < rk T && rk T <= (rk R) + 2
                            && rk L < rk T && rk T <= (rk L) + 2 @-}

{-@ predicate WavlRankN N L R = rk R < N && N <= rk R + 2
                            && rk L < N && N <= rk L + 2 
                            && ((notEmptyTree l) || (notEmptyTree r) || (v == 0)) @-}
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

{-@ idWavl :: t:NEWavl -> s:NEWavl @-}
idWavl :: Tree a -> Tree a
idWavl t = t

-- Deletion functions
{-@ delete :: (Ord a) => a -> s:Wavl -> {t:Wavl | (EqRk s t) || (RkDiff s t 1)} @-}
delete _ (Nil _) = nil
delete y (Tree x n l r)
  | y < x     = balLDel x n l' r
  | x < y     = balRDel x n l r'
  | otherwise = merge y l r n 
    where
      l' = delete x l
      r' = delete x r

{-@ merge :: x:a -> l:Wavl -> r:Wavl -> {v:Rank | WavlRankN v l r }  -> {t:Wavl | EqRkN v t || RkDiffN v t 1 } @-}
merge :: a -> Tree a -> Tree a -> Int ->  Tree a
merge _ (Nil _) (Nil _) _ = nil
merge _ (Nil _) r _  = r
merge _ l (Nil _) _  = l
merge x l r n    = (balRDel y n l r')
  where
   (r', y)     = getMin r

-- get the inorder successor node 
{-@  getMin :: v:NEWavl -> ({t:MaybeWavlNode | (EqRk v t) || (RkDiff v t 1) }, a) @-} 
getMin :: Tree a -> (Tree a, a)
getMin (Tree x 0 (Nil _) (Nil _)) = (nil, x)
getMin (Tree x 1 (Nil _) r@(Tree _ 0 _ _)) = (r, x)
getMin (Tree x n l@(Tree _ _ _ _) r@(Nil _)) = ((balLDel x n l' r), x')
getMin (Tree x n l@(Tree _ _ _ _) r) = ((balLDel x n l' r), x')
  where
    (l', x')             = getMin l

{-@ balLDel :: a -> {n:Rank | n >= 0 } -> {l:Wavl | Is3ChildN n l} -> {r:MaybeWavlNode | Is2ChildN n r} -> {t:NEWavl | (rk t == n || rk t + 1 == n) }  @-}
balLDel :: a -> Int -> Tree a -> Tree a -> Tree a
balLDel x 0 (Nil _) (Nil _)  = singleton x
balLDel x 1 (Nil _) (Nil _)  = singleton x
balLDel x n l r | n <= (rk l) + 2 = t 
                | n == (rk l) + 3 && (rk r) + 2 == n && notEmptyTree r  = demoteL t 
                | n == (rk l) + 3 && notEmptyTree r && (rk r) + 1 == n = doMoreBalL x n l r
                  where
                    t = Tree x n l r
                
{-@ doMoreBalL :: a -> n:Rank -> {l:Wavl | Child3 n l} -> {r:NEWavl | Child1 n r && IsWavlNode r} -> {t:NEWavl | (rk t == n || rk t + 1 == n) } @-}
doMoreBalL x n l r 
  | notEmptyTree (left r)  && notEmptyTree (right r) && rk (left r) + 2 == (rk r) && (rk (right r)) + 2 == rk r = doubleDemoteL t
  | notEmptyTree (right r) && rk (right r) + 1 == rk r = rotateLeftD t
  | notEmptyTree (left r)  && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = rotateDoubleLeftD t
    where t = (Tree x n l r)

{-@ doMoreBalR :: a -> n:Rank -> {l:NEWavl | Child1 n l && IsWavlNode l } -> {r:Wavl | Child3 n r} -> {t:NEWavl | (rk t == n || rk t + 1 == n) } @-}
doMoreBalR x n l r                 
  | notEmptyTree (left l) && notEmptyTree (right l) && (rk (left l)) + 2 == rk l && (rk (right l)) + 2 == rk l = doubleDemoteR t
  | notEmptyTree (left l) && (rk (left l)) + 1 == rk l = rotateRightD t   
  | notEmptyTree (right l) && (rk (left l)) + 2 == rk l && (rk (right l)) + 1 == rk l && isEqEmp r (left l) = rotateDoubleRightD t
    where t = (Tree x n l r)

{-@ balRDel :: a -> n:Rank -> {l:MaybeWavlNode | rk l + 2 >= n && rk l < n} -> {r:Wavl | rk r + 3 >= n && rk r < n} -> {t:NEWavl | rk t == n || rk t + 1 == n } @-}
balRDel :: a -> Int -> Tree a -> Tree a -> Tree a
balRDel x 0 (Nil _) (Nil _) = singleton x
balRDel x 1 (Nil _) (Nil _) = singleton x
balRDel x n l r | n < (rk r + 3) = t
                | n == (rk r + 3) && (rk l) + 2 == n && notEmptyTree l = demoteR t
                | n == (rk r + 3) && (rk l) + 1 == n && notEmptyTree l = doMoreBalR x n l r
                  where 
                    t = Tree x n l r

{-@ demoteL :: s:Node3_2 -> {t:NEWavl | RkDiff s t 1 } @-}
demoteL :: Tree a -> Tree a
demoteL (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteL :: {s:Node3_1 | IsNode2_2 (right s) } -> {t:NEWavl | RkDiff s t 1} @-}
doubleDemoteL :: Tree a -> Tree a
doubleDemoteL (Tree x n l (Tree y m rl rr)) = (Tree x (n-1) l (Tree x (m-1) rl rr))

{-@ rotateLeftD :: {s:Node3_1 | Child1 (rk (right s)) (right (right s)) } -> {t:NEWavl | EqRk s t } @-}
rotateLeftD :: Tree a -> Tree a
rotateLeftD t@(Tree z n zl@(Nil _) (Tree y m yl@(Nil _) w)) = Tree y (m+1) (singleton z) w 
rotateLeftD t@(Tree z n x (Tree y m v w)) = Tree y (m+1) (Tree z (n-1) x v) w 

{-@ rotateDoubleLeftD :: {s:Node3_1 | notEmptyTree (left (right s)) && IsNode1_2 (right s) && EqEmp (left s) (right (right s)) } 
                              -> {t:NEWavl | EqRk s t} @-}
rotateDoubleLeftD :: Tree a -> Tree a
rotateDoubleLeftD (Tree z n x (Tree y m (Tree v o vl vr) yr))     = Tree v n (Tree z (n-2) x vl) (Tree y (n-2) vr yr)

{-@ demoteR :: s:Node2_3 -> {t:NEWavl | RkDiff s t 1 } @-}
demoteR :: Tree a -> Tree a
demoteR (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteR :: {s:Node1_3 | IsNode2_2 (left s) } -> {t:NEWavl | RkDiff s t 1 } @-}
doubleDemoteR :: Tree a -> Tree a
doubleDemoteR (Tree x n (Tree y m ll lr) r) = Tree x (n-1) (Tree y (m-1) ll lr) r 

{-@ rotateRightD :: {s:Node1_3 | Child1 (rk (left s)) (left (left s))  } -> {t:NEWavl | EqRk s t } @-}
rotateRightD :: Tree a -> Tree a
rotateRightD (Tree x n (Tree y m ll (Nil _)) (Nil _)) = Tree y (m+1) ll (singleton x) -- using another demote here
rotateRightD (Tree x n (Tree y m ll lr) r) = Tree y (m+1) ll (Tree x (n-1) lr r) 

{-@ rotateDoubleRightD :: {s:Node1_3 | notEmptyTree (right (left s)) && IsNode2_1 (left s) && EqEmp (right s) (left (left s))} -> {t:NEWavl | EqRk s t } @-}
rotateDoubleRightD :: Tree a -> Tree a
rotateDoubleRightD (Tree x n (Tree y m ll (Tree z o lrl lrr)) r)     = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)

-- Test
main = do
    mapM_ print [a,b,c,d,e,f,g]
  where
    a = singleton 5
    b = insert 2 a
    c = insert 3 b
    d = insert 7 c
    e = insert 10 d
    f = delete 3 e
    g = delete 10 f