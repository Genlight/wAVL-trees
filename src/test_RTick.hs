{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--bscope" @-}

module Test_Rtick where

import Prelude hiding (pure, ap, (<*>))
import Language.Haskell.Liquid.RTick as RTick

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

-- this is valid, but uses a workaround by declaring another Tree b, which i check to be equal to r' and then don't use b
{-@ tickWrapper :: x:a -> {n:Int | n >= 0} -> l:Tree a -> r:Tick ({r':Tree a |  tval r == r'}) -> {t:Tick ({t':Tree a | val t' == x && rk t' == n && left t' == l && tval r == right t'}) | tcost t == tcost r } @-}
tickWrapper :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
tickWrapper x n l  r = (pure tree) `ap` (pure x) `ap` (pure n) `ap` (pure l) `ap` r

{-@ tree :: x:a -> {n:Int | n >= 0} -> l:Tree a -> r:Tree a -> {t:Tree a | rk t == n && left t == l && right t == r && val t == x} @-}
tree :: a -> Int -> Tree a -> Tree a -> Tree a
tree x n l r = Tree x n l r 

-- Defined in RTick library that can open the Tick
exact :: Tick a -> Tick a
{-@ exact :: t:Tick a -> {to:Tick ({v: a | v == (tval t)})| to = t} @-}
exact (Tick c v) = Tick c v 

{-@ exactWAVL :: v:Tick (v':Wavl) -> {t:Tick {t':Wavl | tval t == t'} | tval v == tval t} @-}
exactWAVL :: Tick (Tree a) -> Tick (Tree a)
exactWAVL t = exact t

-- {-@ useTW :: x:a -> {n:Int | n >= 0 } -> l:Tree a -> r:Tick (r':Tree a) -> {t:Tick ({t':Tree a | val t' == x && rk t' == n && left t' == l }) | tcost t == tcost r } @-}
-- useTW :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
-- useTW x n l tt = tickWrapper x n l (tval tt) (exact tt)

{-@ type WavlTick T = {t':Tick ({t:Tree a | t = T}) | balanced T} @-}
-- {-@ visitAll :: v:Wavl -> t:WavlTick ({t':Tree a | t' = v}) @-}
{-@ visitAll :: v:Wavl -> t:WavlTick v @-}
visitAll :: Tree a -> Tick (Tree a)
visitAll Nil = RTick.return Nil
visitAll (Tree x n l r) = Tree <$> (RTick.wait x) <*> (pure n) <*> (visitAll l) <*> (visitAll r)

{-@ reflect tree' @-}
{-@ tree' :: x:a -> n:NodeRank -> {l:MaybeWavlNode | Is2ChildN n l} -> {r:Wavl | Is3ChildN n r} -> {t:NEAlmostWavl | rk t == n && left t == l && right t == r && val t == x} @-}
-- {-@ tree' :: x:a -> n:NodeRank -> {l:MaybeWavlNode | Is2ChildN n l} -> {r:Wavl | Is3ChildN n r} -> {t:NEAlmostWavl | (((rk r) + 3 <= n) || (balanced t)) && rk t == n && left t == l && right t == r && val t == x} @-}
tree' :: a -> Int -> Tree a -> Tree a -> Tree a
tree' x n l r = Tree x n l r 

-- copied from PotentialAnalysis_WAVL.hs, on the 16.03
-- {-@ tree :: x:a -> n:NodeRank -> {l:MaybeWavlNode' | rk l < n && n <= rk l + 2 } -> {r:Wavl' | rk r < n && n <= rk r + 3 } -> {t:NEAlmostWavl' | WAVL.rk t == n && WAVL.left t == l && WAVL.right t == r && WAVL.val t == x} @-}
-- tree :: a -> Int -> Tree a -> Tree a -> Tree a
-- tree x n l r = Tree x n l r 