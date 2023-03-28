{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--bscope" @-}
{-@ LIQUID "--prune-unsorted" @-} -- needed if unused reflections are imported from WAVL

module PotentialAnalysis_WAVL_D  where

import Prelude hiding (pure, (>>=), (<*>), ap)
import WAVL
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.RTick as RTick

{-@ type Wavl' = {v:Tree a | WAVL.balanced v } @-}
{-@ type NEWavl' = {v:Wavl' | WAVL.notEmptyTree v } @-}
{-@ type MaybeWavlNode' = {v:Wavl' | (not (WAVL.notEmptyTree v) || IsWavlNode v) } @-}
{-@ type AlmostWavl' = {t:Tree a | (not (WAVL.notEmptyTree t)) || (WAVL.balanced (WAVL.left t) && WAVL.balanced (WAVL.right t)) } @-}
{-@ type NEAlmostWavl' = {t:AlmostWavl' | WAVL.notEmptyTree t } @-}
{-@ type NodeRank = {v:Int | v >= 0} @-}
{-@ type Node0_1 = { v:AlmostWavl | WAVL.notEmptyTree v  && WAVL.notEmptyTree (left v) && (RkDiff v (left v) 0 ) && (RkDiff v (right v) 1) && rk v >= 0 } @-}
{-@ type Node1_0 = { v:AlmostWavl | WAVL.notEmptyTree v && WAVL.notEmptyTree (right v) && (RkDiff v (left v) 1 ) && (RkDiff v (right v) 0) && rk v >= 0 } @-}
{-@ type Node2_1 = { v:NEWavl | IsNode2_1 v } @-}
{-@ type Node1_2 = { v:NEWavl | IsNode1_2 v } @-}
{-@ type Node0_2 = { v:AlmostWavl | WAVL.notEmptyTree v && WAVL.notEmptyTree (left v) && EqRk v (left v) && RkDiff v (right v) 2  && rk v >= 1 } @-}
{-@ type Node2_0 = { v:AlmostWavl | WAVL.notEmptyTree v && WAVL.notEmptyTree (right v) && EqRk v (right v) && RkDiff v (left v) 2 && rk v >= 1 } @-}
{-@ type Node1_3 = { v:AlmostWavl | WAVL.notEmptyTree v && WAVL.notEmptyTree (left v) && RkDiff v (left v) 1 && RkDiff v (right v) 3  && rk v >= 2 } @-}
{-@ type Node3_1 = { v:AlmostWavl | WAVL.notEmptyTree v && WAVL.notEmptyTree (right v) && RkDiff v (left v) 3 && RkDiff v (right v) 1 && rk v >= 2 } @-}
{-@ type Node3_2 = { v:AlmostWavl | WAVL.notEmptyTree v && WAVL.notEmptyTree (right v) && RkDiff v (left v) 3 && RkDiff v (right v) 2 && rk v >= 2 } @-}
{-@ type Node2_3 = { v:AlmostWavl | WAVL.notEmptyTree v && WAVL.notEmptyTree (left v) && RkDiff v (left v) 2 && RkDiff v (right v) 3  && rk v >= 2 } @-}

-- potential analysis for deletion
{-@ measure potT @-}
{-@ potT :: t:Wavl' -> Int @-}
potT :: Tree a -> Int
potT Nil      = 0
potT t@(Tree _ n l r) 
  | rk l == rk r && rk l + 2 == n = 1 + potT l + potT r        -- 2,2-Node
  | otherwise = potT l + potT r                                -- 1,*-Nodes

{-@ measure potT2 @-}
{-@ potT2 :: t:AlmostWavl' -> Int @-}
potT2 :: Tree a -> Int 
potT2 t@Nil = 0
potT2 t@(Tree _ n l r)
  | rk l + 3 == n && rk r + 2 == n    = 1 + potT l + potT r    -- 2,3-Node
  | rk r + 3 == n && rk l + 2 == n    = 1 + potT l + potT r    -- 3,2-Node
  | rk r + 2 == n && rk l + 2 == n    = 1 + potT l + potT r    -- 2,2-Node
  | otherwise = potT l + potT r
  
{-|
    THEOREM 4.1. In a wavl tree with bottom-up rebalancing, there are at most d demote
    steps over all deletions, where d is the number of deletions.

    -> insertions don't create 2,2-nodes, only destroy them
    -> only at a 2,2- or 1,2-node can a 3-child be created and thus leading to a chain of demote steps
|-}

-- Deletion functions
{-@ delete' :: a -> s:Wavl' -> {t':Tick ({t:Wavl' | ((EqRk s t) || (RkDiff s t 1)) }) | tcost t' >= 0 } @-}
delete' :: (Ord a) => a -> Tree a -> Tick (Tree a)
delete' _ Nil = pure Nil
delete' y (Tree x n l@Nil r@Nil)
  | y < x     = balLDel' x n l' r
  | x < y     = balRDel' x n l r'
  | otherwise = merge' y l r n 
    where
      l' = delete' x l
      r' = delete' x r
delete' y (Tree x n l@Nil r@(Tree _ _ _ _))
  | y < x     = balLDel' x n l' r
  | x < y     = balRDel' x n l r'
  | otherwise = merge' y l r n 
    where
      l' = delete' x l
      r' = delete' x r
delete' y (Tree x n l@(Tree _ _ _ _) r@Nil)
  | y < x     = balLDel' x n l' r
  | x < y     = balRDel' x n l r'
  | otherwise = merge' y l r n 
    where
      l' = delete' x l
      r' = delete' x r
delete' y (Tree x n l@(Tree _ _ _ _) r@(Tree _ _ _ _))
  | y < x     = balLDel' x n l' r
  | x < y     = balRDel' x n l r'
  | otherwise = merge' y l r n 
    where
      l' = delete' x l
      r' = delete' x r

{-@ merge' :: a -> l:Wavl' -> r:Wavl' -> {v:NodeRank | WavlRankN v l r } -> {t':Tick ({t:Wavl' | EqRkN v t || RkDiffN v t 1 }) | tcost t' >= 0 } @-}
merge' :: a -> Tree a -> Tree a -> Int -> Tick (Tree a)
merge' _ Nil Nil _ = pure Nil
merge' _ Nil r _  = pure r
merge' _ l Nil _  = pure l
merge' x l r n    = balRDel' y n l r'
  where
   (r', y)     = getMin' r

{-@  getMin' :: v:NEWavl' -> ({t':Tick ({t:Wavl' | (EqRk v t) || (RkDiff v t 1) }) | tcost t' >= 0 }, _) @-} 
getMin' :: Tree a -> (Tick (Tree a), a)
getMin' (Tree x 0 Nil Nil) = (pure Nil, x)
getMin' (Tree x 1 Nil r@(Tree _ _ _ _)) = (pure r, x)
getMin' (Tree x n l@(Tree _ _ _ _) r@Nil) = ((balLDel' x n l' r), x')
  where
    (l', x')             = getMin' l
getMin' (Tree x n l@(Tree _ _ _ _) r) = ((balLDel' x n l' r), x')
  where
    (l', x')             = getMin' l

{-@ balLDel' :: x:a -> n:NodeRank -> {l:Tick ({l':Wavl' | Is3ChildN n l'}) | tcost l >= 0 } -> {r':MaybeWavlNode' | Is2ChildN n r'} 
          -> {t:Tick ({t':NEWavl' | (rk t' == n || rk t' + 1 == n) && (potT2 t' + (tcost t - tcost l) <= (potT2 (Tree x n (tval l) r')) + 2) }) 
          | tcost t >= 0 
           } @-}
balLDel' :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
balLDel' x 0 l@(Tick _ Nil) Nil  = RTick.step (tcost l) (pure (singleton x))
balLDel' x 1 l@(Tick _ Nil) Nil  = RTick.step (tcost l) (pure (singleton x))
balLDel' x n l r | n <= rk l' + 2 = t
                 | n == rk l' + 3 && rk r + 2 == n = RTick.wmap demoteL' t -- amort. cost 0
                 | n == rk l' + 3 && rk r + 1 == n && rk (left r) + 2 == rk r && (rk (right r)) + 2 == rk r = RTick.wmap doubleDemoteL' t --same 
                 | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 1 == rk r = RTick.wmap rotateLeftD' t -- +1
                 | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = RTick.wmap rotateDoubleLeftD' t -- +1
                 | otherwise = RTick.step (tcost l) (pure (singleton x))
                  where
                    t = RTick.step (tcost l) (pure (Tree x n l' r))
                    l' = tval l

{-@ balRDel' :: x:a -> n:NodeRank -> {l:MaybeWavlNode' | Is2ChildN n l} -> {r:Tick ({r':Wavl' | Is3ChildN n r'}) | tcost r >= 0 } -> {t: Tick ({t':NEWavl' | (rk t' == n || rk t' + 1 == n) && (potT2 t' + (tcost t - tcost r) <= (potT2 (Tree x n l (tval r))) + 2) }) | tcost t >= 0 } @-}
balRDel' :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
balRDel' x 0 Nil r@(Tick _ Nil) = RTick.step (tcost r) (pure (singleton x))
balRDel' x 1 Nil r@(Tick _ Nil) = RTick.step (tcost r) (pure (singleton x))
balRDel' x n l r  | n <  rk r' + 3 = t
                  | n == rk r' + 3 && rk l + 2 == n = RTick.wmap demoteR' t -- amort. cost 0
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 2 == rk l = RTick.wmap doubleDemoteR' t -- same
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 1 == rk l = RTick.wmap rotateRightD' t -- +1
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 1 == rk l = RTick.wmap rotateDoubleRightD' t -- +1
                  | otherwise = t
                  where 
                    t = RTick.step (tcost r) (pure (Tree x n l r')) 
                    r' = tval r

{-@ demoteL' :: s:Node3_2 -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t + 1 } @-}
demoteL' :: Tree a -> Tree a
demoteL' (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteL' :: {s:Node3_1 | IsNode2_2 (right s) } -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t + 1 } @-}
doubleDemoteL' :: Tree a -> Tree a
doubleDemoteL' (Tree x n l (Tree y m rl rr)) = (Tree x (n-1) l (Tree x (m-1) rl rr))

{-@ rotateLeftD' :: {s:Node3_1 | Child1 (rk (right s)) (right (right s)) 
          && (potT (left s)) + (potT (right s)) == potT2 s} 
          -> {t:NEWavl | EqRk s t && (potT2 s == potT2 t || potT2 s + 1 == potT2 t) } @-} 
rotateLeftD' t@(Tree z n l@Nil (Tree y m rl@Nil rr)) = Tree y (m+1) (singleton z) rr
rotateLeftD' t@(Tree z n l (Tree y m rl rr)) = Tree y (m+1) (Tree z (n-1) l rl) rr 

{-@ rotateDoubleLeftD' :: {s:Node3_1 | IsNode1_2 (right s) 
          && (potT (left s)) + (potT (right s)) == potT2 s } 
          -> {t:NEWavl | EqRk s t && (potT2 s == potT2 t || potT2 s + 1 == potT2 t) } @-} 
rotateDoubleLeftD' :: Tree a -> Tree a
rotateDoubleLeftD' (Tree z n l (Tree y m (Tree x o rll rlr) rr)) = Tree x n (Tree z (n-2) l rll) (Tree y (n-2) rlr rr)

{-@ demoteR' :: s:Node2_3 -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t + 1 } @-}
demoteR' :: Tree a -> Tree a
demoteR' (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteR' :: {s:Node1_3 | IsNode2_2 (left s) } 
          -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t + 1 } @-}
doubleDemoteR' :: Tree a -> Tree a
doubleDemoteR' (Tree x n (Tree y m ll lr) r) = Tree x (n-1) (Tree y (m-1) ll lr) r 

{-@ rotateRightD' :: {s:Node1_3 | Child1 (rk (left s)) (left (left s))  
          && (potT (left s)) + (potT (right s)) == potT2 s} 
          -> {t:NEWavl | EqRk s t && (potT2 s == potT2 t || potT2 s + 1 == potT2 t) } @-}
rotateRightD' :: Tree a -> Tree a
rotateRightD' (Tree x n (Tree y m ll Nil) Nil) = Tree y (m+1) ll (singleton x)
rotateRightD' (Tree x n (Tree y m ll lr) r) = Tree y (m+1) ll (Tree x (n-1) lr r) 

{-@ rotateDoubleRightD' :: {s:Node1_3 | IsNode2_1 (left s) && (potT (left s)) + (potT (right s)) == potT2 s }
          -> {t:NEWavl | EqRk s t && (potT2 s == potT2 t || potT2 s + 1 == potT2 t) } @-}
rotateDoubleRightD' :: Tree a -> Tree a
rotateDoubleRightD' (Tree x n (Tree y m ll (Tree z o lrl lrr)) r) = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)

-- Proof of theorem 4.3: 
-- {-@ theorem4_3 :: x:a -> t:Wavl' -> { (potT (delete' x t)) + tcost (delete' x t) <= (potT t) + 1 } @-}
-- theorem4_3 :: a -> Tree a -> ()
-- theorem4_3 x t@Nil = () *** QED
-- theorem4_3 x t@(Tree _ _ l r) = () *** QED


{- sub proof of 4.3: show that if you use a shortened version of balRDel that in a balanced tree no rotations will 
    happen, either with single or double rotate
    and the ovreall Tick cost will remain 0 for such a recursive operation
-}

-- assume that all Nil can have no assoc. potential
-- {-@ invariant {v:Tick (Tree a) | (notEmptyTree (tval v)) || (tcost v == 0)} @-}

{- lemma: using the rebalancing function on an already balanced tree (Wavl') will result in 0 Ticks -}

-- {-@ balancedRLemma :: x:a -> n:NodeRank -> {l:MaybeWavlNode' | Is2ChildN n l} -> {r:WTick ({r':Wavl' | Is2ChildN n r'}) | tcost r >= 0 } -> {tcost (balRDel' x n l r) == tcost r} @-}
-- balancedRLemma :: a -> Int -> Tree a -> Tick (Tree a) -> ()
-- balancedRLemma x 0 Nil r@(Tick _ Nil) = tcost (pure (singleton x)) === 0 
--                                         =<= tcost r === tcost (RTick.step (tcost r) (pure (singleton x)))  *** QED
-- balancedRLemma x 1 Nil r@(Tick _ Nil) = () *** QED
-- balancedRLemma x n l r = tcost r === tcost (RTick.step (tcost r) (pure (Tree x n l (tval r)))) *** QED

-- {-@ type WTick T = {v:Tick (T) | (notEmptyTree (tval v)) || (tcost v == 0)} @-}