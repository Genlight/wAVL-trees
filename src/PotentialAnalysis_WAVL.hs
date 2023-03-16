{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--ple-with-undecided-guards" @-}

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
{-@ delete' :: _ -> s:Wavl' -> {t':Tick ({t:Wavl' | (EqRk s t) || (RkDiff s t 1) }) | tcost t' >= 0 } @-}
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

{-@ balLDel' :: a -> n:NodeRank -> {l:Tick ({l':Wavl' | Is3ChildN n l'}) | tcost l >= 0 } -> {r':MaybeWavlNode' | Is2ChildN n r'} -> {t':Tick ({t:NEWavl' | (rk t == n || rk t + 1 == n) }) | tcost t' >= 0 } @-}
balLDel' :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
balLDel' x 0 (Tick _ Nil) Nil  = pure (singleton x)
balLDel' x 1 (Tick _ Nil) Nil  = pure (singleton x)
balLDel' x n l r | n <= rk l' + 2 = t
                 | n == rk l' + 3 && rk r + 2 == n = RTick.wmap demoteL t
                 | n == rk l' + 3 && rk r + 1 == n && rk (left r) + 2 == rk r && (rk (right r)) + 2 == rk r = RTick.wmap doubleDemoteL t
                 | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 1 == rk r = RTick.wmap rotateLeftD t
                 | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = RTick.wmap rotateDoubleLeftD t
                   where
                     t  | tcost l == 0 = pure (Tree x n l'' r)
                        | otherwise = RTick.waitN (tcost l) (Tree x n l'' r)
                     l' = tvalW l
                     l'' = tval l

{-@ balRDel' :: a -> n:NodeRank -> {l:MaybeWavlNode' | Is2ChildN n l} -> {r:Tick ({r':Wavl' | Is3ChildN n r'}) | tcost r >= 0 } -> {t': Tick ({t:NEWavl' | (rk t == n || rk t + 1 == n) }) | tcost t' >= 0 } @-}
balRDel' :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
balRDel' x 0 Nil (Tick _ Nil) = pure (singleton x)
balRDel' x 1 Nil (Tick _ Nil) = pure (singleton x)
balRDel' x n l r  | n < (rk (right (tval t)) + 3) = t
                  | n == rk r' + 3 && rk l + 2 == n = RTick.wmap WAVL.demoteR t 
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 2 == rk l =RTick.wmap WAVL.doubleDemoteR t
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 1 == rk l = RTick.wmap WAVL.rotateRightD t
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 1 == rk l = RTick.wmap WAVL.rotateDoubleRightD t
                  where 
                    t | tcost r == 0 =  pure (Tree x n l r'') 
                      | otherwise = RTick.waitN (tcost r) (Tree x n l r'') 
                    r' = tvalW r
                    r'' = tval r

{-@ tvalW :: v:Tick (v':Wavl') -> {t:Wavl' | tval v == t} @-}
tvalW :: Tick (Tree a) -> Tree a
tvalW t = tval t