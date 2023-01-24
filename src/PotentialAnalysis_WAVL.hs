{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--ple-with-undecided-guards" @-}

module PotentialAnalysis_WAVL ( ) where

import Prelude hiding (pure)
import WAVL
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.RTick as RTick

-- data TT a = Tick (WAVL.Tree a)
-- unionTickL :: a -> Int -> Tick (Tree a) -> Tree a -> TT a
-- unionTickL x n l r 

-- potential analysis for deletion
{-@ measure potT @-}
-- {-@ potT :: t:WavlD n -> {v:Int | v <= n}  @-}
{-@ potT :: t:Wavl -> Int @-}
potT :: Tree a -> Int
potT WAVL.Nil      = 0
potT t@(WAVL.Tree _ n l r) 
  | 0 == n              = potT l + potT r    -- Leaf-Node
  | WAVL.rk l == rk r && WAVL.rk l + 2 == n = 1 + potT l + potT r        -- 2,2-Node
  | WAVL.rk l + 3 == n && WAVL.rk r + 2 == n    = 1 + potT l + potT r    -- 2,3-Node
  | WAVL.rk r + 3 == n && WAVL.rk l + 2 == n    = 1 + potT l + potT r    -- 3,2-Node
  | otherwise = potT l + potT r

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
{-@ delete' :: (Ord a) => a -> s:Wavl -> Tick ({t:Wavl | (EqRk s t) || (RkDiff s t 1) }) @-}
delete' :: a -> Tree a -> Tick (Tree a)
delete' _ WAVL.Nil = pure WAVL.Nil
delete' y (WAVL.Tree x n l@WAVL.Nil r@WAVL.Nil)
  | y < x     = balLDel' x n l' r
  | x < y     = balRDel' x n l r'
  | otherwise = merge' y l r n 
    where
      l' = delete' x l
      r' = delete' x r
delete' y (WAVL.Tree x n l@WAVL.Nil r@(WAVL.Tree _ _ _ _))
  | y < x     = balLDel' x n l' r
  | x < y     = balRDel' x n l r'
  | otherwise = merge' y l r n 
    where
      l' = delete' x l
      r' = delete' x r
delete' y (WAVL.Tree x n l@(WAVL.Tree _ _ _ _) r@WAVL.Nil)
  | y < x     = balLDel' x n l' r
  | x < y     = balRDel' x n l r'
  | otherwise = merge' y l r n 
    where
      l' = delete' x l
      r' = delete' x r
delete' y (WAVL.Tree x n l@(WAVL.Tree _ _ _ _) r@(WAVL.Tree _ _ _ _))
  | y < x     = balLDel' x n l' r
  | x < y     = balRDel' x n l r'
  | otherwise = merge' y l r n 
    where
      l' = delete' x l
      r' = delete' x r

{-@ merge' :: x:a -> l:Wavl -> r:Wavl -> {v:Rank | WavlRankN v l r && v >= 0 }  -> Tick ({t:Wavl | EqRkN v t || RkDiffN v t 1 }) @-}
merge' :: a -> Tree a -> Tree a -> Int -> Tick (Tree a)
merge' _ Nil Nil _ = pure Nil
merge' _ Nil r _  = pure r
merge' _ l Nil _  = pure l
merge' x l r n    = balRDel' y n l r'
  where
   (r', y)     = getMin' r

-- get the inorder successor node 
{-@  getMin' :: v:NEWavl -> (Tick ({t:Wavl | (EqRk v t) || (RkDiff v t 1) }), a) @-} 
getMin' :: Tree a -> (Tick (Tree a), a)
getMin' (WAVL.Tree x 0 WAVL.Nil WAVL.Nil) = (pure WAVL.Nil, x)
getMin' (WAVL.Tree x 1 WAVL.Nil r@(Tree _ _ _ _)) = (pure r, x)
getMin' (WAVL.Tree x n l@(Tree _ _ _ _) r@WAVL.Nil) = ((balLDel' x n l' r), x')
  where
    (l', x')             = getMin' l
getMin' (WAVL.Tree x n l@(WAVL.Tree _ _ _ _) r) = ((balLDel' x n l' r), x')
  where
    (l', x')             = getMin' l

{-@ balLDel' :: a -> n:Rank -> Tick ({l:Wavl | Is3ChildN n l}) -> {r:MaybeWavlNode | Is2ChildN n r} -> Tick ({t:NEWavl | (rk t == n || rk t + 1 == n) }) @-}
balLDel' :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
balLDel' x 0 (Tick _ Nil) Nil  = pure (singleton x)
balLDel' x 1 (Tick _ Nil) Nil  = pure (singleton x)
balLDel' x n (Tick s l) r | n <= (rk l) + 2 = Tick s t
                 | n == (rk l) + 3 && (rk r) + 2 == n = demoteL' t
                 | n == (rk l) + 3 && (rk r) + 1 == n && rk (left r) + 2 == (rk r) && (rk (right r)) + 2 == rk r = doubleDemoteL' t
                 | n == (rk l) + 3 && (rk r) + 1 == n && rk (right r) + 1 == rk r = rotateLeftD' t
                 | n == (rk l) + 3 && (rk r) + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = rotateDoubleLeftD' t
                   where
                     t = tUnionL x n l r

{-@ balRDel' :: _ -> n:Rank -> {l:MaybeWavlNode | Is2ChildN n l} -> Tick ({r:Wavl | Is3ChildN n r}) -> Tick ({t:NEWavl | rk t == n || rk t + 1 == n }) @-}
balRDel' :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
balRDel' x 0 Nil (Tick _ Nil) = pure (singleton x)
balRDel' x 1 Nil (Tick _ Nil) = pure (singleton x)
balRDel' x n l r | n < (rk r + 3) = t
                 | n == (rk r + 3) && (rk l) + 2 == n = demoteR' t
                 | n == (rk r + 3) && (rk l) + 1 == n && (rk (left l)) + 2 == rk l && (rk (right l)) + 2 == rk l = doubleDemoteR' t
                 | n == (rk r + 3) && (rk l) + 1 == n && (rk (left l)) + 1 == rk l = rotateRightD' t
                 | n == (rk r + 3) && (rk l) + 1 == n && (rk (left l)) + 2 == rk l && (rk (right l)) + 1 == rk l = rotateDoubleRightD' t
                  where 
                    t = tUnionR x n l r

tUnionL :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
tUnionL x n (Tick s l) r = Tick s (Tree x n l r) 

tUnionR :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
tUnionR x n l (Tick s r) = Tick s (Tree x n l r) 

{-@ demoteL' :: s:Node3_2 -> Tick ({t:NEWavl | RkDiff s t 1 }) @-}
demoteL' :: Tree a -> Tick (Tree a)
demoteL' t = go (demoteL t)

{-@ doubleDemoteL' :: {s:Node3_1 | IsNode2_2 (right s) } -> Tick ({t:NEWavl | RkDiff s t 1}) @-}
doubleDemoteL' :: Tree a -> Tick (Tree a)
doubleDemoteL' t = go (doubleDemoteL t)

{-@ rotateLeftD' :: Tick {s:Node3_1 | Child1 (rk (right s)) (right (right s)) } -> Tick ({t:NEWavl | EqRk s t }) @-}
rotateLeftD' :: Tick (Tree a) -> Tick (Tree a)
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

