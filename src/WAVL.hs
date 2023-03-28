{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--bscope" @-}

module WAVL (Tree (..), singleton,
 insert, 
--  delete,
  rk, 
 promoteL, promoteR, 
 demoteL, demoteR, doubleDemoteL, doubleDemoteR, 
 rotateRight, rotateLeft,
 rotateDoubleLeft, 
 rotateDoubleRight,
 rotateLeftD, rotateRightD,  
 rotateDoubleLeftD, 
 rotateDoubleRightD, 
 notEmptyTree, empty,
 potT, potT2
 ) where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.RTick as RTick
import Prelude hiding (pure)

{-@ reflect singleton @-}
{-@ reflect rotateDoubleLeftD @-}
{-@ reflect rotateDoubleRightD @-}
{-@ reflect rotateRightD @-}
{-@ reflect rotateLeftD @-}
{-@ reflect nil @-}

-- Basic functions
{-@ data Tree [rk] a = Nil | Tree { val :: a, 
                                    rd :: {v:Int | v >= 0 }, 
                                    left :: ChildT a rd,
                                    right :: ChildT a rd } @-} 
data Tree a = Nil | Tree { val :: a, rd :: Int, left :: (Tree a), right :: (Tree a)} deriving Show

{-@ type ChildT a K = {v:Tree a | rk v <= K  && K <= rk v + 3} @-}
{-@ type Wavl = {v: Tree a | balanced v } @-}
{-@ type NEWavl = {v:Wavl | notEmptyTree v } @-}
{-@ type AlmostWavl = {t:Tree a | (not (notEmptyTree t)) || (balanced (left t) && balanced (right t)) } @-}
{-@ type Rank = {v:Int | v >= -1} @-}
{-@ type NodeRank = {v:Int | v >= 0} @-}

{-@ measure rk @-}
{-@ rk :: t:Tree a -> {v:Rank | (not (notEmptyTree t) || v >= 0) && (notEmptyTree t || v== (-1))} @-}
rk :: Tree a -> Int
rk Nil =  -1
rk t@(Tree _ n _ _) = n

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

{-@ measure empty @-}
empty :: Tree a -> Bool
empty Nil = True
empty _ = False

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced Nil = True
balanced t@(Tree _ n l r) = rk r < n && n <= rk r + 2 
                         && rk l < n && n <= rk l + 2
                         && ((notEmptyTree l) || (notEmptyTree r) || (n == 0)) -- disallow 2,2-leafs
                         && (balanced l)
                         && (balanced r)

-- alternative balance definition, using an enumeration of all allowed Node states 
-- instead of ranges for ranks
-- {-@ measure balanced' @-}
-- balanced' :: Tree a -> Bool
-- balanced' Nil = True
-- balanced' t@(Tree _ n l r) = isWavlNode t
--   && (balanced' l)
--   && (balanced' r)

{-@ measure isWavlNode @-}  
isWavlNode :: Tree a -> Bool
isWavlNode Nil = True 
isWavlNode t@(Tree x n l r) =  ((rk l) + 2 == n && (rk r) + 2 == n && notEmptyTree l && notEmptyTree r) ||
                ((rk l) + 1 == n && (rk r) + 2 == n) ||
                ((rk l) + 2 == n && (rk r) + 1 == n) ||
                ((rk l) + 1 == n && (rk r) + 1 == n)

{-@ singleton :: a -> {v:NEWavl | ht v == 0 && rk v == 0 } @-}
singleton a = Tree a 0 Nil Nil

-- potential analysis for deletion and insertion
{-@ measure potT @-}
{-@ potT :: t:Wavl -> Int @-}
potT :: Tree a -> Int
potT Nil      = 0
potT t@(Tree _ n l r) 
  | rk l == rk r && rk l + 1 == n = 1 + potT l + potT r        -- 1,1-Node
  | otherwise = potT l + potT r                                -- 2,*-Nodes

{-@ measure potT2 @-}
{-@ potT2 :: t:AlmostWavl -> Int @-}
potT2 :: Tree a -> Int 
potT2 t@Nil = 0
potT2 t@(Tree _ n l r)
  | rk l == n && rk r + 1 == n     = 1 + potT l + potT r    -- 0,1-Node
  | rk r == n && rk l + 1 == n     = 1 + potT l + potT r    -- 1,0-Node
  | rk r + 1 == n && rk l + 1 == n = 1 + potT l + potT r    -- 1,1-Node
  | otherwise = potT l + potT r

-- insertion
{-@ insert :: (Ord a) => a -> s:Wavl -> {t:NEWavl | ((RkDiff t s 1) || (RkDiff t s 0)) } @-}
insert :: (Ord a) => a -> Tree a -> Tree a
insert x Nil = singleton x
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
             | rk l' == n && rk l' == rk r + 2 && (rk (left l') + 1) == rk l' && (rk (right l') + 2) == rk l' = rotateRight lt' 
             | rk l' == n && rk l' == rk r + 2 && (rk (right l') + 1) == rk l' && (rk (left l') + 2) == rk l' = rotateDoubleRight lt' 
             | otherwise = t
        insR | rk r' < n = rt'
             | rk r' == n && rk r' == rk l + 1 = promoteR rt'
             | rk r' == n && rk r' == rk l + 2 && (rk (left r') + 2) == rk r' && (rk (right r') + 1) == rk r' && n >= 1 = rotateLeft rt'
             | rk r' == n && rk r' == rk l + 2 && (rk (left r') + 1) == rk r' && (rk (right r') + 2) == rk r' && n >= 1 = rotateDoubleLeft rt'
             | otherwise = t

{-@ promoteL :: s:Node0_1 -> {t:Node1_2 | RkDiff t s 1 && potT2 s == potT t + 1} @-}
promoteL :: Tree a -> Tree a
promoteL (Tree a n l r) = (Tree a (n+1) l r)

{-@ promoteR :: s:Node1_0 -> {t:NEWavl | RkDiff t s 1 && potT2 s == potT t + 1 } @-}
promoteR :: Tree a -> Tree a
promoteR (Tree a n l r) = (Tree a (n+1) l r)

{-@ rotateRight :: {v:Node0_2 | IsNode1_2 (left v) } -> {t:NEWavl | EqRk v t && potT2 v + 2 == potT t} @-}
rotateRight :: Tree a -> Tree a
rotateRight (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)

{-@ rotateDoubleRight :: {v:Node0_2 | IsNode2_1 (left v) } -> {t:NEWavl | EqRk v t && (potT2 v + 2 == potT t || potT2 v + 1 == potT t)} @-}
rotateDoubleRight :: Tree a -> Tree a 
rotateDoubleRight (Tree z n (Tree x m a (Tree y o b c)) d) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 

{-@ rotateLeft :: {v:Node2_0 | IsNode2_1 (right v) } -> {t:NEWavl | EqRk v t && potT2 v + 2 == potT t} @-}
rotateLeft :: Tree a -> Tree a
rotateLeft t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c

{-@ rotateDoubleLeft :: {v:Node2_0 | IsNode1_2 (right v) } 
          -> {t:NEWavl | EqRk v t && (potT2 v + 2 == potT t || potT2 v + 1 == potT t)} @-}
rotateDoubleLeft :: Tree a -> Tree a
rotateDoubleLeft (Tree x n a (Tree y m (Tree z o b_1 b_2) c)) = Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 

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

-- Deletion functions
-- {-@ delete :: (Ord a) => a -> s:Wavl -> {t:Wavl | (EqRk s t) || (RkDiff s t 1)} @-}
-- delete _ Nil = nil
-- delete y (Tree x n l r)
--   | y < x     = balLDel x n l' r
--   | x < y     = balRDel x n l r'
--   | otherwise = merge y l r n 
--     where
--       l' = delete x l
--       r' = delete x r
      
-- Deletion functions, but with cases for Tree expanded
-- {-@ delete :: (Ord a) => a -> s:Wavl -> {t:Wavl | (EqRk s t) || (RkDiff s t 1)} @-}
-- delete _ Nil = nil
-- delete y (Tree x n l@Nil r@Nil)
--   | y < x     = balLDel x n l' r
--   | x < y     = balRDel x n l r'
--   | otherwise = merge y l r n 
--     where
--       l' = delete x l
--       r' = delete x r
-- delete y (Tree x n l@Nil r@(Tree _ _ _ _))
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

-- {-@ merge :: x:a -> l:Wavl -> r:Wavl -> {v:Rank | WavlRankN v l r && v >= 0 }  -> {t:Wavl | EqRkN v t || RkDiffN v t 1 } @-}
-- merge :: a -> Tree a -> Tree a -> Int ->  Tree a
-- merge _ Nil Nil _ = nil
-- merge _ Nil r _  = r
-- merge _ l Nil _  = l
-- merge x l r n    = (balRDel y n l r')
--   where
--    (r', y)     = getMin r

-- -- get the inorder successor node 
-- {-@  getMin :: v:NEWavl -> ({t:Wavl | (EqRk v t) || (RkDiff v t 1) }, a) @-} 
-- getMin :: Tree a -> (Tree a, a)
-- getMin (Tree x 0 Nil Nil) = (nil, x)
-- getMin (Tree x 1 Nil r@(Tree _ _ _ _)) = (r, x)
-- getMin (Tree x n l@(Tree _ _ _ _) r@Nil) = ((balLDel x n l' r), x')
--   where
--     (l', x')             = getMin l
-- getMin (Tree x n l@(Tree _ _ _ _) r) = ((balLDel x n l' r), x')
--   where
--     (l', x')             = getMin l

-- {-@ balLDel :: x:a -> n:NodeRank -> {l:Tick ({l':Wavl | Is3ChildN n l'}) | tcost l >= 0 } -> {r':MaybeWavlNode | Is2ChildN n r'} 
--           -> {t:Tick ({t':NEWavl | (rk t' == n || rk t' + 1 == n) && (potT2 t' + (tcost t - tcost l) <= (potT2 (Tree x n (tval l) r')) + 3) }) 
--           | tcost t >= 0 } @-} -- TODO: change to 2??
-- balLDel x 0 l@(Tick _ Nil) Nil  = RTick.step (tcost l) (pure (singleton x))
-- balLDel x 1 l@(Tick _ Nil) Nil  = RTick.step (tcost l) (pure (singleton x))
-- balLDel x n l r | n <= rk l' + 2 = t
--                  | n == rk l' + 3 && rk r + 2 == n = RTick.wmap demoteL t -- amort. cost 0
--                  | n == rk l' + 3 && rk r + 1 == n && rk (left r) + 2 == rk r && (rk (right r)) + 2 == rk r = RTick.wmap doubleDemoteL t --same 
--                  | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 1 == rk r = RTick.wmap rotateLeftD t -- +1
--                  | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = RTick.wmap rotateDoubleLeftD t -- +1
--                  | otherwise = RTick.step (tcost l) (pure (singleton x))
--                   where
--                     t = RTick.step (tcost l) (pure (Tree x n l' r))
--                     l' = tval l

{-@ balRDel :: x:a -> n:NodeRank -> {l:MaybeWavlNode | Is2ChildN n l} -> {r:Tick ({r':Wavl | Is3ChildN n r'}) | tcost r >= 0 } -> {t: Tick ({t':NEWavl | (rk t' == n || rk t' + 1 == n) && (potT2 t' + (tcost t - tcost r) <= (potT2 (Tree x n l (tval r))) + 2) }) | tcost t >= 0 } @-}
balRDel :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
balRDel x 0 Nil r@(Tick _ Nil) = RTick.step (tcost r) (pure (singleton x))
balRDel x 1 Nil r@(Tick _ Nil) = RTick.step (tcost r) (pure (singleton x))
balRDel x n l r  | n <  rk r' + 3 = t
                  | n == rk r' + 3 && rk l + 2 == n = RTick.wmap demoteR t -- amort. cost 0
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 2 == rk l = RTick.wmap doubleDemoteR t -- same
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 1 == rk l = RTick.wmap rotateRightD t -- +1
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 1 == rk l = RTick.wmap rotateDoubleRightD t -- +1
                  -- | otherwise = t
                  where 
                    t = RTick.step (tcost r) (pure (Tree x n l r')) 
                    r' = tval r
  
{-@ demoteL :: s:Node3_2 -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t } @-}
demoteL :: Tree a -> Tree a
demoteL (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteL :: {s:Node3_1 | IsNode2_2 (right s) } -> {t:NEWavl | RkDiff s t 1 && potT2 s + 1 == potT2 t } @-}
doubleDemoteL :: Tree a -> Tree a
doubleDemoteL (Tree x n l (Tree y m rl rr)) = (Tree x (n-1) l (Tree x (m-1) rl rr))

{-@ rotateLeftD :: {s:Node3_1 | Child1 (rk (right s)) (right (right s)) 
          && (potT (left s)) + (potT (right s)) == potT2 s} 
          -> {t:NEWavl | EqRk s t && (potT2 s - 1 == potT t || potT2 s == potT t || potT2 s + 1 == potT t) } @-}
rotateLeftD t@(Tree z n l@Nil (Tree y m rl@Nil rr)) = Tree y (m+1) (singleton z) rr
rotateLeftD t@(Tree z n l (Tree y m rl rr)) = Tree y (m+1) (Tree z (n-1) l rl) rr 

{-@ rotateDoubleLeftD :: {s:Node3_1 | IsNode1_2 (right s) 
          && (potT (left s)) + (potT (right s)) == potT2 s } 
          -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s + 1 == potT t ) } @-} 
rotateDoubleLeftD :: Tree a -> Tree a
rotateDoubleLeftD (Tree z n l (Tree y m (Tree x o rll rlr) rr)) = Tree x n (Tree z (n-2) l rll) (Tree y (n-2) rlr rr)

{-@ demoteR :: s:Node2_3 -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t } @-}
demoteR :: Tree a -> Tree a
demoteR (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteR :: {s:Node1_3 | IsNode2_2 (left s) } 
          -> {t:NEWavl | RkDiff s t 1 && potT2 s + 1 == potT2 t } @-}
doubleDemoteR :: Tree a -> Tree a
doubleDemoteR (Tree x n (Tree y m ll lr) r) = Tree x (n-1) (Tree y (m-1) ll lr) r 

{-@ rotateRightD :: {s:Node1_3 | Child1 (rk (left s)) (left (left s))  
          && (potT (left s)) + (potT (right s)) == potT2 s} 
          -> {t:NEWavl | EqRk s t && (potT2 s - 1 == potT t || potT2 s == potT t || potT2 s + 1 == potT t) } @-}
rotateRightD :: Tree a -> Tree a
rotateRightD (Tree x n (Tree y m ll Nil) Nil) = Tree y (m+1) ll (singleton x)
rotateRightD (Tree x n (Tree y m ll lr) r) = Tree y (m+1) ll (Tree x (n-1) lr r) 

{-@ rotateDoubleRightD :: {s:Node1_3 | IsNode2_1 (left s) && (potT (left s)) + (potT (right s)) == potT2 s }
          -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s + 1 == potT t ) } @-}
rotateDoubleRightD :: Tree a -> Tree a
rotateDoubleRightD (Tree x n (Tree y m ll (Tree z o lrl lrr)) r) = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)

{-| Theorem 3.1
  what we want to proof:
  - Height of a given Tree t is a logarithmic upper bound
|-}

-- {-@ reflect heightLemma @-}
-- {-@ heightLemma :: t:Wavl  -> Bool  / [rk t] @-}
-- heightLemma :: Tree a -> Bool
-- heightLemma Nil = True
-- heightLemma t = rk t <= 2 * (ht t) && ht t <= rk t  

-- {-@ wavlNodeStructLemma :: t:Wavl -> { isWavlNode t} @-}
-- wavlNodeStructLemma :: Tree a -> Proof
-- wavlNodeStructLemma t@Nil = trivial *** QED
-- wavlNodeStructLemma t@(Tree _ n l r)  = rk r + 2   ? balanced t 
--                                     =>= n          ? balanced t 
--                                     =<= rk l + 2   ? balanced t
--                                     =>= n          ? balanced t
--                                     =>= rk l + 1   ? balanced t
--                                     =<= n          ? balanced t
--                                     =>= rk r + 1
--                                     *** QED

-- {-@ nilLemma2 :: { t:Wavl | rk t == (-1)} -> {ht t == rk t } @-}
-- nilLemma2 :: Tree a -> Proof 
-- nilLemma2 t@Nil = rk t === (-1) === ht t 
--               *** QED 

-- {-@ hL0 :: {t:NEWavl | ht (left t) == ht (right t)} -> { ht (left t) + 1 == ht t  } @-}
-- hL0 :: Tree a -> Proof
-- hL0 t@(Tree _ _ l r) =  ht l =<= ht l + 1 === ht t *** QED

-- {-@ hL1 :: {t:NEWavl | ht (left t) > ht (right t)} -> {ht t == ht (left t) + 1} @-}
-- hL1 :: Tree a -> Proof
-- hL1 t@(Tree _ _ l r) = ht l =<= (ht l) + 1 === ht t *** QED

-- {-@ hL2 :: {t:NEWavl | ht (left t) < ht (right t)} -> {ht t == ht (right t) + 1} @-}
-- hL2 :: Tree a -> Proof
-- hL2 t@(Tree _ _ l r) = ht r =<= ht r + 1 === ht t *** QED

-- {-@ lowerHeightProof :: t:Wavl -> { ht t <= rk t } / [rk t] @-}
-- lowerHeightProof :: Tree a -> ()
-- lowerHeightProof t@Nil = trivial ? nilLemma2 *** QED
-- lowerHeightProof t@(Tree _ 0 l r) = rk r 
--                                 === (-1)  ? nilLemma2 r        
--                                 === ht r  
--                                 === rk l  ? nilLemma2 l         
--                                 === ht l
--                                 =<= ht t  ? hL0 t        
--                                 === 0 
--                                 =<= rk t
--                                 *** QED
-- lowerHeightProof t@(Tree _ n l r) 
--   | ht l > ht r   = rk t      ? balanced t
--                 =>= rk l + 1  ? lowerHeightProof l
--                 =>= ht l + 1  ? hL1 t
--                 === ht t 
--                 *** QED
--   | ht r > ht l   = rk t      ? balanced t
--                 =>= rk r + 1  ? lowerHeightProof r
--                 =>= ht r + 1  ? hL2 t
--                 === ht t 
--                 *** QED
--   | ht l == ht r  = rk t      ? balanced t
--                 =>= rk l + 1  ? lowerHeightProof l
--                 =>= ht l + 1  ? hL0 t
--                 === ht t 
--                 *** QED

-- {-@ upperHeightProof :: t:Wavl -> { (empty t) || (rk t <= ht t * 2) } / [rk t] @-}
-- upperHeightProof :: Tree a -> Proof
-- upperHeightProof t@Nil  = () ? notEmptyTree t *** QED       
-- upperHeightProof t@(Tree _ 0 l r) = rk r 
--                                 === (-1)  ? nilLemma2 r        
--                                 === ht r  
--                                 === rk l  ? nilLemma2 l         
--                                 === ht l
--                                 =<= ht t  ? hL0 t        
--                                 === 0
--                                 === rk t
--                                 === ht t * 2 
--                                 *** QED
-- upperHeightProof t@(Tree _ 1 l r)
--   | rk l == rk r  = rk t      ? balanced t
--                 =<= rk r + 1
--                 === rk l + 1 
--                 =>= rk l      ? balanced t
--                 === 0         ? upperHeightProof l 
--                 === rk l      ? lowerHeightProof l 
--                 === ht l      
--                 =<= ht l + 1
--                 =<= ht t
--                 =<= ht t * 2 
--                 *** QED
--   | rk l > rk r  = rk t           ? balanced t
--                =<= rk l + 2       ? upperHeightProof l
--                =<= 2 * ht l + 2  
--                =<= 2 * (ht l + 1)   
--                =<= 2 * ht t   
--                *** QED
--   | rk l < rk r  = rk t           ? balanced t
--                =<= rk r + 2       ? upperHeightProof r
--                =<= 2 * ht r + 2  
--                =<= 2 * (ht r + 1)   
--                =<= 2 * ht t   
--                *** QED
-- upperHeightProof t@(Tree _ n l r) 
--   | ht l == ht r  = rk t           ? balanced t
--                 =<= rk l + 2       ? upperHeightProof l
--                 =<= 2 * ht l + 2   
--                 === 2 * (ht l + 1) ? hL0 t
--                 =<= 2 * ht t
--                 *** QED
--   | ht l > ht r   = rk t           ? balanced t
--                 =<= rk l + 2       ? upperHeightProof l
--                 =<= 2 * ht l + 2  
--                 === 2 * (ht l + 1) ? hL1 t
--                 =<= 2 * ht t
--                 *** QED
--   | ht r > ht l   = rk t            ? balanced t
--                 =<= rk r + 2        ? upperHeightProof r
--                 =<= 2 * (ht r) + 2  
--                 === 2 * (ht r + 1) ? hL2 t      
--                 =<= 2 * ht t
--                 *** QED

-- {-@ heightProof :: t:Wavl -> {heightLemma t} @-}
-- heightProof :: Tree a -> Proof
-- heightProof t@Nil = ht t ? lowerHeightProof t  
--               =<= rk t ? notEmptyTree t 
--               *** QED
-- heightProof t = ht t ? lowerHeightProof t 
--             =<= rk t ? upperHeightProof t
--             =<= 2 * ht t  
--             *** QED

-- Test
-- main = do
--     mapM_ print [a,b,c,d,e,f,g]
--   where
--     a = singleton 5
--     b = insert 2 a
--     c = insert 3 b
--     d = insert 7 c
--     e = insert 10 d
--     f = delete 3 e
--     g = delete 10 f