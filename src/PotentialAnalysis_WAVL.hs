{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--bscope" @-}
{-@ LIQUID "--prune-unsorted" @-} -- needed if unused reflections are imported from WAVL

module PotentialAnalysis_WAVL  where

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
  | otherwise = potT l + potT r
  
{-|
    THEOREM 4.1. In a wavl tree with bottom-up rebalancing, there are at most d demote
    steps over all deletions, where d is the number of deletions.

    -> insertions don't create 2,2-nodes, only destroy them
    -> only at a 2,2- or 1,2-node can a 3-child be created and thus leading to a chain of demote steps
|-}

-- Deletion functions
{-@ reflect delete' @-}
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

{-@ reflect merge' @-}
{-@ merge' :: a -> l:Wavl' -> r:Wavl' -> {v:NodeRank | WavlRankN v l r } -> {t':Tick ({t:Wavl' | EqRkN v t || RkDiffN v t 1 }) | tcost t' >= 0 } @-}
merge' :: a -> Tree a -> Tree a -> Int -> Tick (Tree a)
merge' _ Nil Nil _ = pure Nil
merge' _ Nil r _  = pure r
merge' _ l Nil _  = pure l
merge' x l r n    = balRDel' y n l r'
  where
   (r', y)     = getMin' r

{-@ reflect getMin' @-}
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

{-@ reflect balLDel' @-}
{-@ balLDel' :: a -> n:NodeRank -> {l:Tick ({l':Wavl' | Is3ChildN n l'}) | tcost l >= 0 } -> {r':MaybeWavlNode' | Is2ChildN n r'} -> {t':Tick ({t:NEWavl' | (rk t == n || rk t + 1 == n) }) | tcost t' >= 0 && (tcost t' == tcost l || tcost t' == tcost l + 1) } @-}
balLDel' :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
balLDel' x 0 l@(Tick _ Nil) Nil  = RTick.step (tcost l) (pure (singleton x))
balLDel' x 1 l@(Tick _ Nil) Nil  = RTick.step (tcost l) (pure (singleton x))
balLDel' x n l r | n <= rk l' + 2 = t
                 | n == rk l' + 3 && rk r + 2 == n = RTick.fmap demoteL t -- amort. cost 0
                 | n == rk l' + 3 && rk r + 1 == n && rk (left r) + 2 == rk r && (rk (right r)) + 2 == rk r = RTick.fmap doubleDemoteL t --same 
                 | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 1 == rk r = RTick.wmap rotateLeftD t -- +1
                 | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = RTick.wmap rotateDoubleLeftD t -- +1
                 | otherwise = RTick.step (tcost l) (pure (singleton x))
                  where
                    t = RTick.step (tcost l) (pure (Tree x n l' r))
                    l' = tval l

{-@ reflect balRDel' @-}
{-@ balRDel' :: a -> n:NodeRank -> {l:MaybeWavlNode' | Is2ChildN n l} -> {r:Tick ({r':Wavl' | Is3ChildN n r'}) | tcost r >= 0 } -> {t': Tick ({t:NEWavl' | (rk t == n || rk t + 1 == n) }) | tcost t' >= 0 && (tcost t' == tcost r || tcost t' == tcost r + 1) } @-}
balRDel' :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
balRDel' x 0 Nil r@(Tick _ Nil) = RTick.step (tcost r) (pure (singleton x))
balRDel' x 1 Nil r@(Tick _ Nil) = RTick.step (tcost r) (pure (singleton x))
balRDel' x n l r  | n <  rk r' + 3 = t
                  | n == rk r' + 3 && rk l + 2 == n = RTick.fmap demoteR t -- amort. cost 0
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 2 == rk l = RTick.fmap doubleDemoteR t -- same
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 1 == rk l = RTick.wmap rotateRightD t -- +1
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 1 == rk l = RTick.wmap rotateDoubleRightD t -- +1
                  | otherwise = RTick.step (tcost r) (pure (singleton x))
                  where 
                    t = RTick.step (tcost r) (pure (Tree x n l r')) 
                    r' = tval r
-- if demote step: potential is reduced by 1 (amort. cost of 0)
-- if rotate: potT t <= potT2 (Tree x n l r) + 1

-- Proof of theorem 4.3: 
-- {-@ theorem4_3 :: x:a -> t:Wavl' -> { tcost (delete' x t) <= 1 } @-}
-- theorem4_3 x t@Nil = () *** QED
-- theorem4_3 x t@(Tree _ _ l r) = () *** QED


{- sub proof of 4.3: show that if you use a shortened version of balRDel that in a balanced tree no rotations will 
    happen, either with single or double rotate
    and the ovreall Tick cost will remain 0 for such a recursive operation
-}