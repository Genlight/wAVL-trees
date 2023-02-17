{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--ple-with-undecided-guards" @-}

module PotentialAnalysis_WAVL  where

import Prelude hiding (pure, (>>=), (<*>), ap)
import WAVL
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.RTick as RTick
 
-- potential analysis for deletion
-- {-@ measure potT @-}
-- -- {-@ potT :: t:WavlD n -> {v:Int | v <= n}  @-}
-- {-@ potT :: t:Wavl -> Int @-}
-- potT :: Tree a -> Int
-- potT WAVL.Nil      = 0
-- potT t@(WAVL.Tree _ n l r) 
--   | 0 == n              = potT l + potT r    -- Leaf-Node
--   | WAVL.rk l == rk r && WAVL.rk l + 2 == n = 1 + potT l + potT r        -- 2,2-Node
--   | WAVL.rk l + 3 == n && WAVL.rk r + 2 == n    = 1 + potT l + potT r    -- 2,3-Node
--   | WAVL.rk r + 3 == n && WAVL.rk l + 2 == n    = 1 + potT l + potT r    -- 3,2-Node
--   | otherwise = potT l + potT r

{-@ type NodeRank = {v:Int | v >= 0} @-}
{-|
    THEOREM 4.1. In a wavl tree with bottom-up rebalancing, there are at most d demote
    steps over all deletions, where d is the number of deletions.

    -> insertions don't create 2,2-nodes, only destroy them
    -> only at a 2,2- or 1,2-node can a 3-child be created and thus leading to a chain of demote steps
|-}


-- don't know if we need this here, probably redundant, bc we want to say that amortized costs of all demote steps are equal to deletions n
-- WavlD a n, where n is the total count for all the deletions applied on the tree
-- {-@ type WavlD n = {t:Wavl | n >= 0 } @-}

-- Deletion functions
-- {-@ delete' :: _ -> s:Wavl -> Tick ({t:Wavl | (EqRk s t) || (RkDiff s t 1) }) @-}
-- delete' :: (Ord a) => a -> Tree a -> Tick (Tree a)
-- delete' _ WAVL.Nil = pure WAVL.Nil
-- delete' y (WAVL.Tree x n l@WAVL.Nil r@WAVL.Nil)
--   | y < x     = balLDel' x n l' r
--   | x < y     = balRDel' x n l r'
--   | otherwise = merge' y l r n 
--     where
--       l' = delete' x l
--       r' = delete' x r
-- delete' y (WAVL.Tree x n l@WAVL.Nil r@(WAVL.Tree _ _ _ _))
--   | y < x     = balLDel' x n l' r
--   | x < y     = balRDel' x n l r'
--   | otherwise = merge' y l r n 
--     where
--       l' = delete' x l
--       r' = delete' x r
-- delete' y (WAVL.Tree x n l@(WAVL.Tree _ _ _ _) r@WAVL.Nil)
--   | y < x     = balLDel' x n l' r
--   | x < y     = balRDel' x n l r'
--   | otherwise = merge' y l r n 
--     where
--       l' = delete' x l
--       r' = delete' x r
-- delete' y (WAVL.Tree x n l@(WAVL.Tree _ _ _ _) r@(WAVL.Tree _ _ _ _))
--   | y < x     = balLDel' x n l' r
--   | x < y     = balRDel' x n l r'
--   | otherwise = merge' y l r n 
--     where
--       l' = delete' x l
--       r' = delete' x r

-- {-@ merge' :: a -> l:Wavl -> r:Wavl -> {v:Rank | WavlRankN v l r && v >= 0 }  -> Tick ({t:Wavl | EqRkN v t || RkDiffN v t 1 }) @-}
-- merge' :: a -> Tree a -> Tree a -> Int -> Tick (Tree a)
-- merge' _ Nil Nil _ = pure Nil
-- merge' _ Nil r _  = pure r
-- merge' _ l Nil _  = pure l
-- merge' x l r n    = balRDel' y n l r'
--   where
--    (r', y)     = getMin' r

-- -- get the inorder successor node 
-- {-@  getMin' :: v:NEWavl -> (Tick ({t:Wavl | (EqRk v t) || (RkDiff v t 1) }), _) @-} 
-- getMin' :: Tree a -> (Tick (Tree a), a)
-- getMin' (WAVL.Tree x 0 WAVL.Nil WAVL.Nil) = (pure WAVL.Nil, x)
-- getMin' (WAVL.Tree x 1 WAVL.Nil r@(Tree _ _ _ _)) = (pure r, x)
-- getMin' (WAVL.Tree x n l@(Tree _ _ _ _) r@WAVL.Nil) = ((balLDel' x n l' r), x')
--   where
--     (l', x')             = getMin' l
-- getMin' (WAVL.Tree x n l@(WAVL.Tree _ _ _ _) r) = ((balLDel' x n l' r), x')
--   where
--     (l', x')             = getMin' l

-- {-@ balLDel' :: _ -> {n:Rank | n >= 0} -> Tick ({l:Wavl | Is3ChildN n l}) -> {r:MaybeWavlNode | Is2ChildN n r} -> Tick ({t:NEWavl | (rk t == n || rk t + 1 == n) }) @-}
-- balLDel' :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
-- balLDel' x 0 (Tick _ Nil) Nil  = pure (singleton x)
-- balLDel' x 1 (Tick _ Nil) Nil  = pure (singleton x)
-- balLDel' x n l r | n <= rk l' + 2 = t
--                  | n == rk l' + 3 && rk r + 2 == n = t >>= demoteL'
--                  | n == rk l' + 3 && rk r + 1 == n && rk (left r) + 2 == rk r && (rk (right r)) + 2 == rk r = t >>= doubleDemoteL'
--                  | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 1 == rk r = t >>= rotateLeftD'
--                  | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = t >>= rotateDoubleLeftD'
--                    where
--                      t  = tUnionL x n l r
--                      l' = tval l 


{-@ balRDel' :: a -> n:NodeRank -> {l:MaybeWavlNode2 | Is2ChildN n l} -> Tick ({r:Wavl' | Is3ChildN n r}) -> Tick (t:NEWavl') @-}
balRDel' :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
balRDel' x 0 Nil (Tick _ Nil) = pure (singleton x)
balRDel' x 1 Nil (Tick _ Nil) = pure (singleton x)
balRDel' x n l r | n < rk r' + 3 = t
                 | n' == rk r' + 3 && rk l' + 2 == n' = t >>= demoteR'
                 | n' == rk r' + 3 && rk l' + 1 == n' && rk (left l') + 2 == rk l' && rk (right l') + 2 == rk l' = t >>= doubleDemoteR'
                 | n' == rk r' + 3 && rk l' + 1 == n' && rk (left l') + 1 == rk l' = t >>= rotateRightD'
                 | n' == rk r' + 3 && rk l' + 1 == n' && rk (left l') + 2 == rk l' && rk (right l') + 1 == rk l' = t >>= rotateDoubleRightD'
                  where 
                    t  = tickWrapperR x n l (tval r) r
                    r' = tval r
                    l' = left (tval t) 
                    n' = rk (tval t)

{-@ tree :: x:a -> n:NodeRank -> l:Wavl' -> r:Wavl' -> {t:NEAlmostWavl' | WAVL.rk t == n && WAVL.left t == l && WAVL.right t == r && WAVL.val t == x} @-}
tree :: a -> Int -> Tree a -> Tree a -> Tree a
tree x n l r = Tree x n l r 

{-@ tickWrapperR :: x:a -> n:NodeRank -> l:Wavl' -> b:Wavl' -> r:Tick ({r':Wavl' | b == r'}) -> {t:Tick ({t':NEAlmostWavl' | WAVL.rk t' == n && WAVL.left t' == l && WAVL.val t' == x && b == WAVL.right t' }) | tcost t == tcost r } @-}
tickWrapperR :: a -> Int -> Tree a -> Tree a -> Tick (Tree a) -> Tick (Tree a)
tickWrapperR x n l _ r = (pure tree) `ap` (pure x) `ap` (pure n) `ap` (pure l) `ap` r

-- {-@ tickWrapperL :: a -> n:NodeRank -> l:Tick (Wavl') -> r:Wavl' -> {t:Tick ({t':NEAlmostWavl' | rk t' == n && left t' == tval l}) | tcost t == tcost l } @-}
-- tickWrapperL :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
-- tickWrapperL x n l r = (pure tree') `ap` (pure x) `ap` (pure n) `ap` l `ap` (pure r)

{-@ type Wavl' = {v:Tree a | WAVL.balanced v } @-}
{-@ type NEWavl' = {v:Wavl' | WAVL.notEmptyTree v } @-}
{-@ type MaybeWavlNode2 = {v:Wavl' | (not (WAVL.notEmptyTree v) || IsWavlNode v) } @-}
{-@ type AlmostWavl' = {t:Tree a | (not (WAVL.notEmptyTree t)) || (WAVL.balanced (WAVL.left t) && WAVL.balanced (WAVL.right t)) } @-}
{-@ type NEAlmostWavl' = {t:AlmostWavl' | WAVL.notEmptyTree t } @-}
 
{-@ demoteL' :: s:Node3_2 -> Tick ({t:NEWavl | RkDiff s t 1 }) @-}
demoteL' :: Tree a -> Tick (Tree a)
demoteL' t = go (WAVL.demoteL t)

{-@ doubleDemoteL' :: {s:Node3_1 | IsNode2_2 (right s) } -> Tick ({t:NEWavl | RkDiff s t 1}) @-}
doubleDemoteL' :: Tree a -> Tick (Tree a)
doubleDemoteL' t = RTick.go (doubleDemoteL t)

{-@ rotateLeftD' :: {s:Node3_1 | Child1 (rk (right s)) (right (right s)) } -> Tick ({t:NEWavl | EqRk s t }) @-}
rotateLeftD' :: Tree a -> Tick (Tree a)
rotateLeftD' t = RTick.wait (rotateLeftD t)

{-@ rotateDoubleLeftD' :: {s:Node3_1 | WAVL.notEmptyTree (left (right s)) && IsNode1_2 (right s) } 
                              -> Tick ({t:NEWavl | EqRk s t}) @-}
rotateDoubleLeftD' :: Tree a -> Tick (Tree a)
rotateDoubleLeftD' t = RTick.wait (rotateDoubleLeftD t)

{-@ demoteR' :: s:Node2_3 -> Tick ({t:NEWavl | RkDiff s t 1 }) @-}
demoteR' :: Tree a -> Tick (Tree a)
demoteR' t = go (demoteR t)

{-@ doubleDemoteR' :: {s:Node1_3 | IsNode2_2 (left s) } -> Tick ({t:NEWavl | RkDiff s t 1 }) @-}
doubleDemoteR' :: Tree a -> Tick (Tree a)
doubleDemoteR' t = go (doubleDemoteR t)

{-@ rotateRightD' :: {s:Node1_3 | Child1 (rk (left s)) (left (left s))  } -> Tick {t:NEWavl | EqRk s t } @-}
rotateRightD' :: Tree a -> Tick (Tree a)
rotateRightD' t = RTick.wait (rotateRightD t)

{-@ rotateDoubleRightD' :: {s:Node1_3 | WAVL.notEmptyTree (right (left s)) && IsNode2_1 (left s) } -> Tick {t:NEWavl | EqRk s t } @-}
rotateDoubleRightD' :: Tree a -> Tick (Tree a)
rotateDoubleRightD' t = RTick.wait (rotateDoubleRightD t)

-- Test methods
{-@ idWavl' :: t:Tree a -> {v:Tick (Tree a) | tval v == t} @-}
idWavl' :: Tree a -> Tick (Tree a)
idWavl' t = pure (t)

{-@ tree'' :: a -> n:NodeRank -> l:Wavl' -> r:Wavl' -> Tick ({t:NEAlmostWavl' | rk t == n && left t == l && right t == r}) @-}
tree'' :: a -> Int -> Tree a -> Tree a -> Tick (Tree a)
tree'' a n l r = pure (Tree a n l r)

id2 :: Tick (Tree a) -> Tick (Tree a)
id2 t = t >>= idWavl'