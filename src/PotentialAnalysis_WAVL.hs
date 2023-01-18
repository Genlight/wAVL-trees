{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

module PotentialAnalysis_WAVL ( ) where

import WAVL
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.RTick as RTick

-- potential analysis for insertion
-- {-@ measure potT @-}
{-@ potT :: t:Wavl ->  v:Int @-}
potT :: Tree a -> Int
potT WAVL.Nil      = 0
potT (WAVL.Tree _ n l r)
  | 0 == n                        = go 0    -- Leaf-Node
  | rk l == rk r && rk l + 1 == n = go 1    -- 1,1-Node
  | rk l == n && rk r + 1 == n    = go 1    -- 0,1-Node
  | rk r == n && rk l + 1 == n    = go 1    -- 1,0-Node
  | otherwise = go 0 
    where go n = n + potT l + potT r

{-|
    THEOREM 4.1. In a wavl tree with bottom-up rebalancing, there are at most d demote
    steps over all deletions, where d is the number of deletions.

    -> insertions don't create 2,2-nodes, only destroy them
    -> only at a 2,2- or 1,2-node can a 3-child be created and thus leading to a chain of demote steps
|-}

{-@ demoteL' :: s:Node3_2 -> t:Tick {t:NEWavl | RkDiff s t 1 } @-}
demoteL' :: Tree a -> Tick (Tree a)
demoteL' t = RTick.wait (demoteL t)

{-@ demoteR' :: s:Node2_3 -> t:Tick {t:NEWavl | RkDiff s t 1 } @-}
demoteR' :: Tree a -> Tick (Tree a)
demoteR' t = RTick.wait (demoteR t)

-- Deletion functions
-- {-@ delete :: (Ord a) => a -> s:Wavl -> {t:Wavl | (EqRk s t) || (RkDiff s t 1)} @-}
-- delete _ WAVL.Nil = pure WAVL.Nil
-- delete y (WAVL.Tree x n l@WAVL.Nil r@WAVL.Nil)
--   | y < x     = balLDel x n l' r
--   | x < y     = balRDel x n l r'
--   | otherwise = merge y l r n 
--     where
--       l' = RTick.step 1 (delete x l)
--       r' = RTick.step 1 (delete x r)
-- delete y (WAVL.Tree x n l@WAVL.Nil r@(Tree _ _ _ _))
--   | y < x     = balLDel x n l' r
--   | x < y     = balRDel x n l r'
--   | otherwise = merge y l r n 
--     where
--       l' = delete x l
--       r' = delete x r
-- delete y (Tree x n l@(Tree _ _ _ _) r@Nil)
--   | y < x     = balLDel x n l' r
--   | x < y     = balRDel x n l r'
--   | otherwise = merge y l r n 
--     where
--       l' = delete x l
--       r' = delete x r
-- delete y (Tree x n l@(Tree _ _ _ _) r@(Tree _ _ _ _))
--   | y < x     = balLDel x n l' r
--   | x < y     = balRDel x n l r'
--   | otherwise = merge y l r n 
--     where
--       l' = delete x l
--       r' = delete x r