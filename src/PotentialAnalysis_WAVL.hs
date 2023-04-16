{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--bscope" @-}
{-@ LIQUID "--prune-unsorted" @-} -- needed if unused reflections are imported from WAVL

module PotentialAnalysis_WAVL  where

import Prelude hiding (pure, (>>=), (<*>), ap)
import WAVL hiding (insert)
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.RTick as RTick

{-@ type Wavl' = {v:Tree a | WAVL.balanced v } @-}
{-@ type NEWavl' = {v:Wavl' | WAVL.notEmptyTree v } @-}
{-@ type MaybeWavlNode' = {v:Wavl' | (not (WAVL.notEmptyTree v) || IsWavlNode v) } @-}
{-@ type AlmostWavl' = {t:Tree a | (not (WAVL.notEmptyTree t)) || (WAVL.balanced (WAVL.left t) && WAVL.balanced (WAVL.right t)) } @-}
{-@ type NEAlmostWavl' = {t:AlmostWavl' | WAVL.notEmptyTree t } @-}
{-@ type NodeRank = {v:Int | v >= 0} @-}
{-@ type Node0_1 = { v:AlmostWavl' | WAVL.notEmptyTree v  && WAVL.notEmptyTree (left v) && (RkDiff v (left v) 0 ) && (RkDiff v (right v) 1) && rk v >= 0 } @-}
{-@ type Node1_0 = { v:AlmostWavl' | WAVL.notEmptyTree v && WAVL.notEmptyTree (right v) && (RkDiff v (left v) 1 ) && (RkDiff v (right v) 0) && rk v >= 0 } @-}
{-@ type Node2_1 = { v:NEWavl' | IsNode2_1 v } @-}
{-@ type Node1_2 = { v:NEWavl' | IsNode1_2 v } @-}
{-@ type Node1_1 = { v:NEWavl' | IsNode1_1 v } @-}
{-@ type Node0_2 = { v:AlmostWavl' | WAVL.notEmptyTree v && WAVL.notEmptyTree (left v) && EqRk v (left v) && RkDiff v (right v) 2  && rk v >= 1 } @-}
{-@ type Node2_0 = { v:AlmostWavl' | WAVL.notEmptyTree v && WAVL.notEmptyTree (right v) && EqRk v (right v) && RkDiff v (left v) 2 && rk v >= 1 } @-}
{-@ type Node1_3 = { v:AlmostWavl' | WAVL.notEmptyTree v && WAVL.notEmptyTree (left v) && RkDiff v (left v) 1 && RkDiff v (right v) 3  && rk v >= 2 } @-}
{-@ type Node3_1 = { v:AlmostWavl' | WAVL.notEmptyTree v && WAVL.notEmptyTree (right v) && RkDiff v (left v) 3 && RkDiff v (right v) 1 && rk v >= 2 } @-}
{-@ type Node3_2 = { v:AlmostWavl' | WAVL.notEmptyTree v && WAVL.notEmptyTree (right v) && RkDiff v (left v) 3 && RkDiff v (right v) 2 && rk v >= 2 } @-}
{-@ type Node2_3 = { v:AlmostWavl' | WAVL.notEmptyTree v && WAVL.notEmptyTree (left v) && RkDiff v (left v) 2 && RkDiff v (right v) 3  && rk v >= 2 } @-}

{-@ predicate Is0ChildN N S= (rk S) == N @-}

{-@ inline isNode1_1 @-}
isNode1_1 :: Tree a -> Bool
isNode1_1 t = (rk (left t)) + 1 == (rk t) && (rk (right t)) + 1 == rk t

{-@ inline isNode1_2 @-}
isNode1_2 :: Tree a -> Bool
isNode1_2 t = (rk (left t)) + 1 == (rk t) && (rk (right t)) + 2 == rk t && notEmptyTree (left t)

{-@ inline isNode2_1 @-}
isNode2_1 :: Tree a -> Bool
isNode2_1 t = (rk (left t)) + 2 == (rk t) && (rk (right t)) + 1 == rk t && notEmptyTree (right t)

{-@ inline isNode2_2 @-}
isNode2_2 :: Tree a -> Bool
isNode2_2 t = (rk (left t)) + 2 == (rk t) && (rk (right t)) + 2 == rk t && notEmptyTree (right t) && notEmptyTree (left t)


-- potential analysis for insertion, with deletion included
{-@ measure potT @-}
{-@ potT :: t:Wavl' -> Int @-}
potT :: Tree a -> Int
potT Nil      = 0
potT t@(Tree _ n l r) 
  | rk l == rk r && rk l + 1 == n = 1 + potT l + potT r        -- 1,1-Node
  | otherwise = potT l + potT r                                -- 2,*-Nodes

{-@ measure potT2 @-}
{-@ potT2 :: t:AlmostWavl' -> Int @-}
potT2 :: Tree a -> Int 
potT2 t@Nil = 0
potT2 t@(Tree _ n l r)
  | rk l == n && rk r + 1 == n     = 1 + potT l + potT r    -- 0,1-Node
  | rk r == n && rk l + 1 == n     = 1 + potT l + potT r    -- 1,0-Node
  | rk r + 1 == n && rk l + 1 == n = 1 + potT l + potT r    -- 1,1-Node
  | otherwise = potT l + potT r
  
{-|
    THEOREM 4.2. In a wavl tree with bottom-up rebalancing, 
    there are at most 3m + 2d ≤ 5m promote steps over all insertions, 
    
    where m and d are the number of insertions and deletions, respectively.

    -> potential is defined for non-leaf 1,1-nodes or 0,1-node to be 1
    -> all other nodes are zero. 
|-}
{-@ insert :: (Ord a) => a -> s:Wavl' -> {t:NEWavl' | (RkDiff t s 0 || RkDiff t s 1) 
          && (not (isNode2_2 t) || (RkDiff t s 0)) 
          && ((not (isNode1_1 t && rk t > 0)) || RkDiff t s 0) && IsWavlNode t } @-} 
insert :: (Ord a) => a -> Tree a -> Tree a
insert x Nil = singleton x
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> insR
    EQ -> t
    where 
      l' = insert x l
      r' = insert x r
      insL | rk l' < n = Tree v n l' r
           | otherwise = balL v n l' r 
      insR | rk r' < n = Tree v n l r'
           | otherwise = balR v n l r'

{-@ balL :: a -> n:NodeRank -> {l:NEWavl' | Is0ChildN n l && ((isNode1_1 l && rk l == 0) || isNode2_1 l || isNode1_2 l) } 
          -> {r:Wavl' | Is2ChildN n r} 
          -> {t:NEWavl' | (rk t == n || rk t == n + 1) && not (isNode2_2 t) 
            && ((not (isNode1_1 t && rk t == 0)) || rk t - n == 1) 
            && ((not (isNode1_1 t && rk t > 0)) || rk t == n) && IsWavlNode t }  @-}
balL :: a -> Int -> Tree a -> Tree a -> Tree a
balL x n l r | rk l == rk r + 1 = promoteL' t
             | rk l == rk r + 2 && (rk (right l) + 2) == rk l = rotateRight' t 
             | rk l == rk r + 2 && (rk (right l) + 1) == rk l = rotateDoubleRight' t 
              where 
                t = Tree x n l r

{-@ balR :: a -> n:NodeRank -> {l:Wavl' | Is2ChildN n l } 
          -> {r:NEWavl' | Is0ChildN n r && ((isNode1_1 r && rk r == 0) || isNode2_1 r || isNode1_2 r) } 
          -> {t:NEWavl' | (rk t == n || rk t == n + 1) && not (isNode2_2 t) 
            && ((not (isNode1_1 t && rk t == 0)) || rk t - n == 1) 
            && ((not (isNode1_1 t && rk t > 0)) || rk t == n) && IsWavlNode t }  @-}
balR :: a -> Int -> Tree a -> Tree a -> Tree a
balR x n l r  | rk r == rk l + 1 = promoteR' t
              | rk r == rk l + 2 && (rk (left r) + 2) == rk r = rotateLeft' t 
              | rk r == rk l + 2 && (rk (left r) + 1) == rk r = rotateDoubleLeft' t 
               where 
                 t = Tree x n l r

{-@ promoteL' :: s:Node0_1 -> {t:Node1_2 | RkDiff t s 1 && potT2 s == potT t + 1} @-}
promoteL' :: Tree a -> Tree a
promoteL' (Tree a n l r) = (Tree a (n+1) l r)

{-@ promoteR' :: s:Node1_0 -> {t:Node2_1 | RkDiff t s 1 && potT2 s == potT t + 1 } @-}
promoteR' :: Tree a -> Tree a
promoteR' (Tree a n l r) = (Tree a (n+1) l r)

{-@ rotateRight' :: {v:Node0_2 | IsNode1_2 (left v) } -> {t:Node1_1 | EqRk v t && potT2 v + 2 == potT t} @-}
rotateRight' :: Tree a -> Tree a
rotateRight' (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)

{-@ rotateDoubleRight' :: {v:Node0_2 | IsNode2_1 (left v) } -> {t:Node1_1 | EqRk v t && (potT2 v + 2 == potT t || potT2 v + 1 == potT t)} @-}
rotateDoubleRight' :: Tree a -> Tree a 
rotateDoubleRight' (Tree z n (Tree x m a (Tree y o b c)) d) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 

{-@ rotateLeft' :: {v:Node2_0 | IsNode2_1 (right v) } -> {t:Node1_1 | EqRk v t && potT2 v + 2 == potT t} @-}
rotateLeft' :: Tree a -> Tree a
rotateLeft' t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c

-- {-@ rotateDoubleLeft' :: {v:Node2_0 | IsNode1_2 (right v) } -> {t:Node1_1 | EqRk v t && (potT2 v + 2 == potT t || potT2 v + 1 == potT t)} @-}
-- rotateDoubleLeft' :: Tree a -> Tree a
-- rotateDoubleLeft' (Tree x n a (Tree y m (Tree z o b_1 b_2) c)) = Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 

-- Deletion functions
-- {-@ delete' :: a -> s:Wavl' -> {t':Tick ({t:Wavl' | ((EqRk s t) || (RkDiff s t 1)) }) | tcost t' >= 0 } @-}
-- delete' :: (Ord a) => a -> Tree a -> Tick (Tree a)
-- delete' _ Nil = pure Nil
-- delete' y (Tree x n l@Nil r@Nil)
--   | y < x     = balLDel' x n l' r
--   | x < y     = balRDel' x n l r'
--   | otherwise = merge' y l r n 
--     where
--       l' = delete' x l
--       r' = delete' x r
-- delete' y (Tree x n l@Nil r@(Tree _ _ _ _))
--   | y < x     = balLDel' x n l' r
--   | x < y     = balRDel' x n l r'
--   | otherwise = merge' y l r n 
--     where
--       l' = delete' x l
--       r' = delete' x r
-- delete' y (Tree x n l@(Tree _ _ _ _) r@Nil)
--   | y < x     = balLDel' x n l' r
--   | x < y     = balRDel' x n l r'
--   | otherwise = merge' y l r n 
--     where
--       l' = delete' x l
--       r' = delete' x r
-- delete' y (Tree x n l@(Tree _ _ _ _) r@(Tree _ _ _ _))
--   | y < x     = balLDel' x n l' r
--   | x < y     = balRDel' x n l r'
--   | otherwise = merge' y l r n 
--     where
--       l' = delete' x l
--       r' = delete' x r

-- {-@ merge' :: a -> l:Wavl' -> r:Wavl' -> {v:NodeRank | WavlRankN v l r } -> {t':Tick ({t:Wavl' | EqRkN v t || RkDiffN v t 1 }) | tcost t' >= 0 } @-}
-- merge' :: a -> Tree a -> Tree a -> Int -> Tick (Tree a)
-- merge' _ Nil Nil _ = pure Nil
-- merge' _ Nil r _  = pure r
-- merge' _ l Nil _  = pure l
-- merge' x l r n    = balRDel' y n l r'
--   where
--    (r', y)     = getMin' r

-- {-@  getMin' :: v:NEWavl' -> ({t':Tick ({t:Wavl' | (EqRk v t) || (RkDiff v t 1) }) | tcost t' >= 0 }, _) @-} 
-- getMin' :: Tree a -> (Tick (Tree a), a)
-- getMin' (Tree x 0 Nil Nil) = (pure Nil, x)
-- getMin' (Tree x 1 Nil r@(Tree _ _ _ _)) = (pure r, x)
-- getMin' (Tree x n l@(Tree _ _ _ _) r@Nil) = ((balLDel' x n l' r), x')
--   where
--     (l', x')             = getMin' l
-- getMin' (Tree x n l@(Tree _ _ _ _) r) = ((balLDel' x n l' r), x')
--   where
--     (l', x')             = getMin' l

-- {-@ balLDel' :: x:a -> n:NodeRank -> {l:Tick ({l':Wavl' | Is3ChildN n l'}) | tcost l >= 0 } -> {r':MaybeWavlNode' | Is2ChildN n r'} 
--           -> {t:Tick ({t':NEWavl' | (rk t' == n || rk t' + 1 == n) && (potT2 t' + (tcost t - tcost l) <= (potT2 (Tree x n (tval l) r')) + 2) }) 
--           | tcost t >= 0 
--            } @-}
-- balLDel' :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
-- balLDel' x 0 l@(Tick _ Nil) Nil  = RTick.step (tcost l) (pure (singleton x))
-- balLDel' x 1 l@(Tick _ Nil) Nil  = RTick.step (tcost l) (pure (singleton x))
-- balLDel' x n l r | n <= rk l' + 2 = t
--                  | n == rk l' + 3 && rk r + 2 == n = RTick.wmap demoteL' t -- amort. cost 0
--                  | n == rk l' + 3 && rk r + 1 == n && rk (left r) + 2 == rk r && (rk (right r)) + 2 == rk r = RTick.wmap doubleDemoteL' t --same 
--                  | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 1 == rk r = RTick.wmap rotateLeftD' t -- +1
--                  | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = RTick.wmap rotateDoubleLeftD' t -- +1
--                  | otherwise = RTick.step (tcost l) (pure (singleton x))
--                   where
--                     t = RTick.step (tcost l) (pure (Tree x n l' r))
--                     l' = tval l

-- {-@ balRDel' :: x:a -> n:NodeRank -> {l:MaybeWavlNode' | Is2ChildN n l} -> {r:Tick ({r':Wavl' | Is3ChildN n r'}) | tcost r >= 0 } -> {t: Tick ({t':NEWavl' | (rk t' == n || rk t' + 1 == n) && (potT2 t' + (tcost t - tcost r) <= (potT2 (Tree x n l (tval r))) + 2) }) | tcost t >= 0 } @-}
-- balRDel' :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
-- balRDel' x 0 Nil r@(Tick _ Nil) = RTick.step (tcost r) (pure (singleton x))
-- balRDel' x 1 Nil r@(Tick _ Nil) = RTick.step (tcost r) (pure (singleton x))
-- balRDel' x n l r  | n <  rk r' + 3 = t
--                   | n == rk r' + 3 && rk l + 2 == n = RTick.wmap demoteR' t -- amort. cost 0
--                   | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 2 == rk l = RTick.wmap doubleDemoteR' t -- same
--                   | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 1 == rk l = RTick.wmap rotateRightD' t -- +1
--                   | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 1 == rk l = RTick.wmap rotateDoubleRightD' t -- +1
--                   | otherwise = t
--                   where 
--                     t = RTick.step (tcost r) (pure (Tree x n l r')) 
--                     r' = tval r

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

{-@ rotateDoubleLeftD' :: {s:Node3_1 | IsNode1_2 (right s) 
          && (potT (left s)) + (potT (right s)) == potT2 s } 
          -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s + 1 == potT t ) } @-} 
rotateDoubleLeftD' :: Tree a -> Tree a
rotateDoubleLeftD' (Tree z n l (Tree y m (Tree x o rll rlr) rr)) = Tree x n (Tree z (n-2) l rll) (Tree y (n-2) rlr rr)

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

{-@ rotateDoubleRightD' :: {s:Node1_3 | IsNode2_1 (left s) && (potT (left s)) + (potT (right s)) == potT2 s }
          -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s + 1 == potT t ) } @-}
rotateDoubleRightD' :: Tree a -> Tree a
rotateDoubleRightD' (Tree x n (Tree y m ll (Tree z o lrl lrr)) r) = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)