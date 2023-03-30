{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--bscope" @-}

module Test_Potentialchange where

import Prelude hiding (pure)
import Language.Haskell.Liquid.RTick as RTick

{-@ reflect singleton @-}
{-@ reflect nil @-}

{-@ data Tree [rk] a = Nil | Tree { val :: a, 
                                    rd :: {v:Int | v >= 0 }, 
                                    left :: Tree a,
                                    right :: Tree a } @-} 
data Tree a = Nil | Tree { val :: a, rd :: Int, left :: (Tree a), right :: (Tree a)} deriving Show

{-@ type Wavl = {v: Tree a | balanced v } @-}
{-@ type NEWavl = {v:Wavl | notEmptyTree v } @-}
{-@ type AlmostWavl = {t:Tree a | (not (notEmptyTree t)) || (balanced (left t) && balanced (right t)) } @-}
{-@ type Rank = {v:Int | v >= -1} @-}
{-@ type NodeRank = {v:Int | v >= 0} @-}
{-@ type MaybeWavlNode = {v:Wavl | (not (notEmptyTree v) || IsWavlNode v) } @-}
{-@ type NEAlmostWavl = {t:AlmostWavl | notEmptyTree t } @-}

{-@ predicate EqRk S T = rk T == rk S @-}
{-@ predicate RkDiff S T D = (rk S) - (rk T) == D @-}

{-@ predicate EqRkN N T = rk T == N @-}
{-@ predicate RkDiffN N T D = N - (rk T) == D @-}

{-@ type Node0_1 = { v:AlmostWavl | notEmptyTree v  && notEmptyTree (left v) && (RkDiff v (left v) 0 ) && (RkDiff v (right v) 1) && rk v >= 0 } @-}
{-@ type Node1_0 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && (RkDiff v (left v) 1 ) && (RkDiff v (right v) 0) && rk v >= 0 } @-}

{-@ type Node2_1 = { v:NEWavl | IsNode2_1 v } @-}
{-@ type Node1_2 = { v:NEWavl | IsNode1_2 v } @-}

{-@ type Node0_2 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v) && EqRk v (left v) && RkDiff v (right v) 2  && rk v >= 1 } @-}
{-@ type Node2_0 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && EqRk v (right v) && RkDiff v (left v) 2 && rk v >= 1 } @-}

{-@ type Node1_3 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v) && RkDiff v (left v) 1 && RkDiff v (right v) 3  && rk v >= 2 } @-}
{-@ type Node3_1 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && RkDiff v (left v) 3 && RkDiff v (right v) 1 && rk v >= 2 } @-}
{-@ type Node3_2 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && RkDiff v (left v) 3 && RkDiff v (right v) 2 && rk v >= 2 } @-}
{-@ type Node2_3 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v) && RkDiff v (left v) 2 && RkDiff v (right v) 3  && rk v >= 2 } @-}

{-@ predicate IsNode2_2 T = (rk (left T)) + 2 == (rk T) && (rk (right T)) + 2 == rk T && notEmptyTree (left T) && notEmptyTree (right T) @-}
{-@ predicate IsNode1_2 T = (rk (left T)) + 1 == (rk T) && (rk (right T)) + 2 == rk T && notEmptyTree (left T) @-}
{-@ predicate IsNode2_1 T = (rk (left T)) + 2 == (rk T) && (rk (right T)) + 1 == rk T && notEmptyTree (right T)@-}
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

{-@ measure rk @-}
{-@ rk :: t:Tree a -> {v:Rank | (not (notEmptyTree t) || v >= 0) && (notEmptyTree t || v== (-1))} @-}
rk :: Tree a -> Int
rk Nil =  -1
rk t@(Tree _ n _ _) = n

{-@ nil :: {v:Wavl | rk v == (-1) && not (notEmptyTree v) } @-}
nil :: Tree a
nil = Nil

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced Nil = True
balanced t@(Tree _ n l r) = rk r < n && n <= rk r + 2 
                         && rk l < n && n <= rk l + 2
                         && ((notEmptyTree l) || (notEmptyTree r) || (n == 0)) -- disallow 2,2-leafs
                         && (balanced l)
                         && (balanced r)

{-@ measure notEmptyTree @-}
notEmptyTree :: Tree a -> Bool
notEmptyTree Nil = False
notEmptyTree _ = True

{-@ measure ht @-}
{-@ ht :: Tree a -> Rank @-}
ht              :: Tree a -> Int
ht Nil          = (-1)
ht (Tree x n l r) = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

{-@ measure empty @-}
empty :: Tree a -> Bool
empty Nil = True
empty _ = False

{-@ singleton :: a -> {v:NEWavl | ht v == 0 && rk v == 0 && potT v == 0 } @-}
singleton a = Tree a 0 Nil Nil

-- potential analysis for deletion
{-@ measure potT @-}
{-@ potT :: t:Wavl -> Int @-}
potT :: Tree a -> Int
potT Nil      = 0
potT (Tree _ 0 Nil Nil) = 0                                    -- only non-leaf 1,1-Nodes have potential 
potT (Tree _ n l r) 
  | rk l == rk r && rk l + 1 == n = 1 + potT l + potT r        -- 1,1-Node
  | otherwise = potT l + potT r                                -- 2,*-Nodes

{-@ measure potT2 @-}
{-@ potT2 :: t:AlmostWavl -> Int @-}
potT2 :: Tree a -> Int 
potT2 t@Nil = 0
potT2 (Tree _ 0 Nil Nil) = 0
potT2 t@(Tree _ n l r)
  | rk l + 1 == n && rk r == n     = 1 + potT l + potT r    -- 0,1-Node
  | rk r + 1 == n && rk l == n     = 1 + potT l + potT r    -- 1,0-Node
  | rk r + 1 == n && rk l + 1 == n = 1 + potT l + potT r    -- 1,1-Node
  | otherwise = potT l + potT r

{-@ promoteL :: s:Node0_1 -> {t:Node1_2 | RkDiff t s 1 && potT2 s == potT t + 1} @-}
promoteL :: Tree a -> Tree a
promoteL (Tree a n l r) = (Tree a (n+1) l r)

{-@ promoteR :: s:Node1_0 -> {t:NEWavl | RkDiff t s 1 && potT2 s == potT t + 1 } @-}
promoteR :: Tree a -> Tree a
promoteR (Tree a n l r) = (Tree a (n+1) l r)

{-@ rotateRight :: {v:Node0_2 | IsNode1_2 (left v) && potT (left v) + potT (right v) == potT2 v } 
          -> {t:NEWavl | EqRk v t && (potT2 v <= potT2 t)} @-}
rotateRight :: Tree a -> Tree a
rotateRight (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)

-- {-@ rotateDoubleRight :: {v:Node0_2 | IsNode2_1 (left v) } -> {t:NEWavl | EqRk v t && (potT2 v + 2 == potT t || potT2 v + 1 == potT t)} @-}
-- rotateDoubleRight :: Tree a -> Tree a 
-- rotateDoubleRight (Tree z n (Tree x m a (Tree y o b c)) d) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 

-- {-@ rotateLeft :: {v:Node2_0 | IsNode2_1 (right v) } -> {t:NEWavl | EqRk v t && potT2 v + 2 == potT t} @-}
-- rotateLeft :: Tree a -> Tree a
-- rotateLeft t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c

-- {-@ rotateDoubleLeft :: {v:Node2_0 | IsNode1_2 (right v) } 
--           -> {t:NEWavl | EqRk v t && (potT2 v + 2 == potT t || potT2 v + 1 == potT t)} @-}
-- rotateDoubleLeft :: Tree a -> Tree a
-- rotateDoubleLeft (Tree x n a (Tree y m (Tree z o b_1 b_2) c)) = Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 

{-@ demoteL' :: s:Node3_2 -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t } @-}
demoteL' :: Tree a -> Tree a
demoteL' (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteL' :: {s:Node3_1 | IsNode2_2 (right s) } -> {t:NEWavl | RkDiff s t 1 && potT2 s + 1 == potT2 t } @-}
doubleDemoteL' :: Tree a -> Tree a
doubleDemoteL' (Tree x n l (Tree y m rl rr)) = (Tree x (n-1) l (Tree x (m-1) rl rr))

{-@ rotateLeftD' :: {s:Node3_1 | Child1 (rk (right s)) (right (right s)) 
          && (potT (left s)) + (potT (right s)) == potT2 s} 
          -> {t:NEWavl | EqRk s t && (potT2 s - 1 == potT t || potT2 s == potT t || potT2 s + 1 == potT t) } @-} -- potT2 s - 1 <= potT t && potT2 s >= potT t
rotateLeftD' t@(Tree z n l@Nil (Tree y m rl@Nil rr)) = Tree y (m+1) (Tree z 0 Nil Nil) rr
rotateLeftD' t@(Tree z n l (Tree y m rl rr)) = Tree y (m+1) (Tree z (n-1) l rl) rr 

-- {-@ rotateDoubleLeftD' :: {s:Node3_1 | IsNode1_2 (right s) 
--           && (potT (left s)) + (potT (right s)) == potT2 s } 
--           -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s + 1 == potT t ) } @-} 
-- rotateDoubleLeftD' :: Tree a -> Tree a
-- rotateDoubleLeftD' (Tree z n l (Tree y m (Tree x o rll rlr) rr)) = Tree x n (Tree z (n-2) l rll) (Tree y (n-2) rlr rr)

{-@ demoteR' :: s:Node2_3 -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t } @-}
demoteR' :: Tree a -> Tree a
demoteR' (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteR' :: {s:Node1_3 | IsNode2_2 (left s) } 
          -> {t:NEWavl | RkDiff s t 1 && potT2 s + 1 == potT2 t } @-}
doubleDemoteR' :: Tree a -> Tree a
doubleDemoteR' (Tree x n (Tree y m ll lr) r) = Tree x (n-1) (Tree y (m-1) ll lr) r 

{-@ rotateRightD' :: {s:Node1_3 | Child1 (rk (left s)) (left (left s))  
          && (potT (left s)) + (potT (right s)) == potT2 s} 
          -> {t:NEWavl | EqRk s t && (potT2 s - 1 == potT t || potT2 s == potT t || potT2 s + 1 == potT t) } @-}
rotateRightD' :: Tree a -> Tree a
rotateRightD' (Tree x n (Tree y m ll Nil) Nil) = Tree y (m+1) ll (singleton x)
rotateRightD' (Tree x n (Tree y m ll lr) r) = Tree y (m+1) ll (Tree x (n-1) lr r) 

-- {-@ rotateDoubleRightD' :: {s:Node1_3 | IsNode2_1 (left s) && (potT (left s)) + (potT (right s)) == potT2 s }
--           -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s + 1 == potT t ) } @-}
-- rotateDoubleRightD' :: Tree a -> Tree a
-- rotateDoubleRightD' (Tree x n (Tree y m ll (Tree z o lrl lrr)) r) = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)

-- && (potT t + (tcost t') <= potT s + 4

-- {-@ insert :: (Ord a) => a -> s:Wavl -> {t':Tick ({t:NEWavl | ((RkDiff t s 1) || (RkDiff t s 0)) && (potT t  <= potT s + 4 )}) | tcost t' >= 0} @-}
-- insert :: (Ord a) => a -> Tree a -> Tick (Tree a)
-- insert x Nil = pure (singleton x)
-- insert x t@(Tree v n l r) = case compare x v of 
--     LT -> insL
--     GT -> insR
--     EQ -> pure t
--     where 
--         l' = insert x l
--         r' = insert x r
--         l'' = tval l'
--         r'' = tval r'
--         lt' = RTick.step (tcost l') (pure (Tree x n l'' r)) 
--         rt' = RTick.step (tcost r') (pure (Tree x n l r'')) 
--         insL | rk l'' < n = lt'
--              | rk l'' == n && rk l'' == rk r + 1 = RTick.wmap promoteL lt'
--              | rk l'' == n && rk l'' == rk r + 2 && (rk (left l'') + 1) == rk l'' && (rk (right l'') + 2) == rk l'' = RTick.wmap rotateRight lt' 
--              | rk l'' == n && rk l'' == rk r + 2 && (rk (right l'') + 1) == rk l'' && (rk (left l'') + 2) == rk l'' = RTick.wmap rotateDoubleRight lt' 
--              | otherwise = pure t
--         insR | rk r'' < n = rt'
--              | rk r'' == n && rk r'' == rk l + 1 = RTick.wmap promoteR rt'
--              | rk r'' == n && rk r'' == rk l + 2 && (rk (left r'') + 2) == rk r'' && (rk (right r'') + 1) == rk r'' && n >= 1 = RTick.wmap rotateLeft rt'
--              | rk r'' == n && rk r'' == rk l + 2 && (rk (left r'') + 1) == rk r'' && (rk (right r'') + 2) == rk r'' && n >= 1 = RTick.wmap rotateDoubleLeft rt'
--              | otherwise = pure t