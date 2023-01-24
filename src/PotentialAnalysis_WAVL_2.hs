{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--ple-with-undecided-guards" @-}

module PotentialAnalysis_WAVL_2 ( ) where

import Prelude hiding (pure)
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.RTick as RTick

-- data TT a = Tick (Tree a)
-- unionTickL :: a -> Int -> Tick (Tree a) -> Tree a -> TT a
-- unionTickL x n l r 

{-@ data Tree [rk] a = Nil | Tree { val :: a, 
                                    rd :: {v:Int | v >= 0 }, 
                                    left :: RTick.Tick (Tree a),
                                    right :: RTick.Tick (Tree a) } @-} 
data Tree a = Nil | Tree {val :: a, rd :: Int,  left :: (RTick.Tick (Tree a)), right :: (RTick.Tick (Tree a))} 

{-@ type Wavl = {t:Tree a | balanced t} @-}
{-@ type NEWavl = {v:Wavl | notEmptyTree v && rk v >= 0 } @-}
{-@ type AlmostWavl = {t:Tree a | (not (notEmptyTree t)) || (balanced (left t) && balanced (right t)) } @-}
{-@ type Rank = {v:Int | v >= -1} @-}

{-@ measure rk @-}
{-@ rk :: Tick (t:Tree a) -> {v:Rank | (not (notEmptyTree t) || v >= 0) && (notEmptyTree t || v== (-1))} @-}
rk :: Tick (Tree a) -> Int
rk (Tick _ (Nil)) =  -1
rk (Tick _ t@(Tree _ n _ _)) = n

{-@ nil :: {v:Wavl | rk v == (-1) && not (notEmptyTree v) && ht v == (-1)} @-}
nil :: Tree a
nil = Nil

{-@ measure notEmptyTree @-}
notEmptyTree :: Tree a -> Bool
notEmptyTree Nil = False
notEmptyTree _ = True

{-@ measure ht @-}
{-@ ht :: Tree a -> Rank @-}
ht              :: Tree a -> Int
ht Nil          = (-1)
ht (Tree x n l r) = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced Nil = True
balanced t@(Tree _ n l r) = rk r < n && n <= rk r + 2 
                         && rk l < n && n <= rk l + 2
                         && ((notEmptyTree l) || (notEmptyTree r) || (n == 0)) -- disallow 2,2-leafs
                         && (balanced l)
                         && (balanced r)

{-@ measure isWavlNode @-}  
isWavlNode :: Tree a -> Bool
isWavlNode Nil = True 
isWavlNode t@(Tree x n l r) =  ((rk l) + 2 == n && (rk r) + 2 == n && notEmptyTree l && notEmptyTree r) ||
                ((rk l) + 1 == n && (rk r) + 2 == n) ||
                ((rk l) + 2 == n && (rk r) + 1 == n) ||
                ((rk l) + 1 == n && (rk r) + 1 == n)

{-@ singleton :: a -> {v:NEWavl | ht v == 0 && rk v == 0 } @-}
singleton a = Tree a 0 nil nil

-- potential analysis for deletion
-- {-@ measure potT @-}
-- -- {-@ potT :: t:WavlD n -> {v:Int | v <= n}  @-}
-- {-@ potT :: t:Wavl -> {v:Int | v >= 0 } @-}
-- potT :: Tree a -> Int
-- potT Nil      = 0
-- potT t@(Tree _ n l r)
--   | 0 == n              = potT l + potT r    -- Leaf-Node
--   | rk l == rk r && rk l + 2 == n = 1 + potT l + potT r        -- 2,2-Node
--   | rk l + 3 == n && rk r + 2 == n    = 1 + potT l + potT r    -- 2,3-Node
--   | rk r + 3 == n && rk l + 2 == n    = 1 + potT l + potT r    -- 3,2-Node
--   | otherwise = potT l + potT r

{-|
    THEOREM 4.1. In a wavl tree with bottom-up rebalancing, there are at most d demote
    steps over all deletions, where d is the number of deletions.

    -> insertions don't create 2,2-nodes, only destroy them
    -> only at a 2,2- or 1,2-node can a 3-child be created and thus leading to a chain of demote steps
|-}

-- don't know if we need this here, probably redundant, bc we want to say that amortized costs of all demote steps are equal to deletions n
-- WavlD a n, where n is the total count for all the deletions applied on the tree
-- {-@ type WavlD n = {t:Wavl | n >= 0 } @-}

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

-- Deletion functions
{-@ delete' :: (Ord a) => a -> s:Wavl -> Tick ({t:Wavl | (EqRk s t) || (RkDiff s t 1) }) @-}
delete' :: a -> Tree a -> Tick (Tree a)
delete' _ Nil = pure Nil
delete' y (Tree x n l@Nil r@Nil)
  | y < x     = balLDel' x n l' r
  | x < y     = balRDel' x n l r'
  | otherwise = merge' y l r n 
    where
      l' = delete' x l
      r' = delete' x r
delete' y (Tree x n l@Nil r@(Tick _ (Tree _ _ _ _)))
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
getMin' (Tree x 0 Nil Nil) = (pure Nil, x)
getMin' (Tree x 1 Nil r@(Tree _ _ _ _)) = (pure r, x)
getMin' (Tree x n l@(Tree _ _ _ _) r@Nil) = ((balLDel' x n l' r), x')
  where
    (l', x')             = getMin' l
getMin' (Tree x n l@(Tree _ _ _ _) r) = ((balLDel' x n l' r), x')
  where
    (l', x')             = getMin' l

{-@ balLDel' :: a -> n:Rank -> Tick ({l:Wavl | Is3ChildN n l}) -> Tick {r:MaybeWavlNode | Is2ChildN n r} -> Tick ({t:NEWavl | (rk t == n || rk t + 1 == n) }) @-}
balLDel' :: a -> Int -> Tick (Tree a) -> Tick (Tree a) -> Tick (Tree a)
balLDel' x 0 Nil Nil  = pure (singleton x)
balLDel' x 1 Nil Nil  = pure (singleton x)
balLDel' x n l r | n <= (rk l) + 2 = Tick s t
                 | n == (rk l) + 3 && (rk r) + 2 == n = demoteL' t
                 | n == (rk l) + 3 && (rk r) + 1 == n && rk (left r) + 2 == (rk r) && (rk (right r)) + 2 == rk r = doubleDemoteL' t
                 | n == (rk l) + 3 && (rk r) + 1 == n && rk (right r) + 1 == rk r = rotateLeftD' t
                 | n == (rk l) + 3 && (rk r) + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = rotateDoubleLeftD' t
                   where
                     t = Tree x n l r

{-@ balRDel' :: _ -> n:Rank -> Tick {l:MaybeWavlNode | Is2ChildN n l} -> Tick ({r:Wavl | Is3ChildN n r}) -> Tick ({t:NEWavl | rk t == n || rk t + 1 == n }) @-}
balRDel' :: a -> Int -> Tick (Tree a) -> Tick (Tree a) -> Tick (Tree a)
balRDel' x 0 Nil (Tick _ Nil) = pure (singleton x)
balRDel' x 1 Nil (Tick _ Nil) = pure (singleton x)
balRDel' x n l r | n < (rk r + 3) = t
                 | n == (rk r + 3) && (rk l) + 2 == n = demoteR' t
                 | n == (rk r + 3) && (rk l) + 1 == n && (rk (left l)) + 2 == rk l && (rk (right l)) + 2 == rk l = doubleDemoteR' t
                 | n == (rk r + 3) && (rk l) + 1 == n && (rk (left l)) + 1 == rk l = rotateRightD' t
                 | n == (rk r + 3) && (rk l) + 1 == n && (rk (left l)) + 2 == rk l && (rk (right l)) + 1 == rk l = rotateDoubleRightD' t
                  where 
                    t = Tree x n l r

-- tUnionL :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
-- tUnionL x n l r = Tick s (Tree x n l r) 

-- tUnionR :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
-- tUnionR x n l (Tick s r) = Tick s (Tree x n l r) 

{-@ demoteL' :: s:Node3_2 -> Tick ({t:NEWavl | RkDiff s t 1 }) @-}
demoteL' :: Tree a -> Tick (Tree a)
demoteL' t = go (demoteL t)

{-@ doubleDemoteL' :: {s:Node3_1 | IsNode2_2 (right s) } -> Tick ({t:NEWavl | RkDiff s t 1}) @-}
doubleDemoteL' :: Tree a -> Tick (Tree a)
doubleDemoteL' t = go (doubleDemoteL t)

{-@ rotateLeftD' :: Tick {s:Node3_1 | Child1 (rk (right s)) (right (right s)) } -> Tick ({t:NEWavl | EqRk s t }) @-}
rotateLeftD' :: Tick (Tree a) -> Tick (Tree a)
rotateLeftD' t = RTick.wait (rotateLeftD t)

{-@ rotateDoubleLeftD' :: {s:Node3_1 | notEmptyTree (left (right s)) && IsNode1_2 (right s) } 
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

{-@ rotateDoubleRightD' :: {s:Node1_3 | notEmptyTree (right (left s)) && IsNode2_1 (left s) } -> Tick {t:NEWavl | EqRk s t } @-}
rotateDoubleRightD' :: Tree a -> Tick (Tree a)
rotateDoubleRightD' t = RTick.wait (rotateDoubleRightD t)

