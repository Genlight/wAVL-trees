{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--bscope" @-}

module PotentialAnalysis_WAVL where

import Prelude hiding (pure, wmap, fmap)
import Language.Haskell.Liquid.RTick as RTick hiding (wmap, fmap)
import Language.Haskell.Liquid.ProofCombinators 

{-@ reflect singleton @-}
{-@ reflect nil @-}

-- {-@ reflect promoteL @-}
-- {-@ reflect promoteR @-}
-- {-@ reflect rotateDoubleLeft @-}
-- {-@ reflect rotateDoubleRight @-}
-- {-@ reflect rotateLeft @-}
-- {-@ reflect rotateRight @-}

-- {-@ reflect balL @-}
-- {-@ reflect balR @-}
-- {-@ reflect insert @-}


{-@ data Tree [rk] a = Nil | Tree { val :: a, 
                                    rd :: {v:Int | v >= 0 }, 
                                    left :: ChildT a rd,
                                    right :: ChildT a rd } @-} 
data Tree a = Nil | Tree { val :: a, rd :: Int, left :: (Tree a), right :: (Tree a)} deriving Show

{-@ type Wavl = {v:Tree a | balanced v } @-}
{-@ type NEWavl = {v:Wavl | notEmptyTree v } @-}
{-@ type ChildT a K = {v:Tree a | rk v <= K  && K <= rk v + 3} @-}
{-@ type ChildW K = {v:Wavl | rk v <= K  && K <= rk v + 3} @-}
{-@ type ChildB K = {v:Wavl | Is2ChildN K v } @-}
{-@ type AlmostWavl = {t:Tree a | isAlmostWavl t } @-}
{-@ type Rank = {v:Int | v >= -1} @-}
{-@ type NodeRank = {v:Int | v >= 0} @-}
{-@ type MaybeWavlNode = {v:Wavl | (not (notEmptyTree v) || IsWavlNode v) } @-}
{-@ type NEAlmostWavl = {t:AlmostWavl | notEmptyTree t } @-}


{- the following type refinements are only valid for insert and the respective sub functions, since EqT / EqT1 and EqT2 are heavily based on EqRk and RkDiff
also, most of the implications for the equality proofs are made on assumptions only valid for insert
-}
-- Tree to Tick
{-@ type EqT s = {t':Tick ({t:NEWavl | (EqRk t s || RkDiff t s 1) 
          && (not (isNode2_2 t) || (EqRk t s)) 
          && (not (isNode2_2nNil s) || (EqRk t s)) 
          && ((not (isNode1_1 t && rk t > 0)) || EqRk t s) && IsWavlNode t }) | tcost t' >= 0 } @-} -- && amortizedStmt t' s
--  s: Tick(Tree a), f: function to apply, m: tcost to add
-- {-@ type EqTf s f m = {t':Tick ({t:NEWavl | (EqRk t (tval s) || RkDiff t (tval s) 1) 
--           && (not (isNode2_2 t) || (EqRk t (tval s))) && (not (isNode2_2nNil (tval s)) || (EqRk t (tval s))) 
--           && ((not (isNode1_1 t && rk t > 0)) || EqRk t (tval s)) && IsWavlNode t }) | tcost t' >= 0 && Tick (tcost s + m) (f (tval s)) == t' } @-}

-- Tree to Tree
{-@ type EqT1 t1 = {t:NEWavl | (EqRk t t1 || RkDiff t t1 1) 
          && (not (isNode2_2 t) || (EqRk t t1))
          && (not (isNode2_2nNil t1) || (EqRk t t1)) 
          && ((not (isNode1_1 t && rk t > 0)) || EqRk t t1) && IsWavlNode t } @-}

-- Tick to Tick
{-@ type EqT2 s = {t':Tick ({t:NEWavl | (EqRk t (tval s) || RkDiff t (tval s) 1) 
          && (not (isNode2_2 t) || (EqRk t (tval s))) 
          && (not (isNode2_2nNil (tval s)) || (EqRk t (tval s))) 
          && ((not (isNode1_1 t && rk t > 0)) || EqRk t (tval s)) && IsWavlNode t }) | tcost t' >= 0 
          } @-} 
-- && amortizedStmt' s t'
{-@ predicate EqRk S T = rk T == rk S @-}
{-@ predicate RkDiff S T D = (rk S) - (rk T) == D @-}

{-@ predicate EqRkN N T = rk T == N @-}
{-@ predicate RkDiffN N T D = N - (rk T) == D @-}

{-@ type Node0_1 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v)  && (RkDiff v (left v) 0 ) && (RkDiff v (right v) 1) && rk v >= 0 } @-}
{-@ type Node1_0 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && (RkDiff v (left v) 1 ) && (RkDiff v (right v) 0) && rk v >= 0 } @-}

{-@ type Node1_1 = { v:NEWavl | isNode1_1 v } @-}
{-@ type Node2_1 = { v:NEWavl | isNode2_1 v } @-}
{-@ type Node1_2 = { v:NEWavl | isNode1_2 v } @-}

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

{-@ predicate Is3Child T S = (rk S) + 3 >= (rk T) && (rk T) > (rk S) @-}
{-@ predicate Is2Child T S = (rk S) + 2 >= (rk T) && (rk T) > (rk S) @-}
{-@ predicate Is1Child T S = (rk S) + 1 >= (rk T) && (rk T) > (rk S) @-}

{-@ predicate Is3ChildN N S = (rk S) + 3 >= N && N > (rk S)  @-}
{-@ predicate Is2ChildN N S = (rk S) + 2 >= N && N > (rk S)  @-}
{-@ predicate Is1ChildN N S = (rk S) + 1 >= N && N > (rk S)  @-}
{-@ predicate Is01ChildN N S= (rk S) + 1 >= N && N >= (rk S) @-}
{-@ predicate Is0ChildN N S= (rk S) == N @-}

{-@ predicate WavlRank T L R = rk R < rk T && rk T <= (rk R) + 2
                            && rk L < rk T && rk T <= (rk L) + 2 @-}

{-@ predicate WavlRankN N L R = rk R < N && N <= rk R + 2
                            && is2ChildN N l 
                            && ((notEmptyTree l) || (notEmptyTree r) || (v == 0)) @-}
{-@ predicate WavlRankL N L R = rk R < N && N <= rk R + 2
                            && rk L < N && N <= rk L + 3 @-}
{-@ predicate WavlRankR N L R = rk R < N && N <= rk R + 3
                            && is2ChildN N l @-}

{-@ predicate Child3 N T = rk T + 3 == N @-}
{-@ predicate Child2 N T = rk T + 2 == N @-}
{-@ predicate Child1 N T = rk T + 1 == N @-}

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

{-- 
  This inline check was needed to convey the property of isNode2_2 in insert but it needed a Pre-check, 
  
  since NIL Trees don't have the functions right and left 
--}
{-@ inline isNode2_2nNil @-}
isNode2_2nNil :: Tree a -> Bool
isNode2_2nNil t = if not (notEmptyTree t) then False else isNode2_2 t


{-@ inline is0ChildN @-}
is0ChildN :: Int -> Tree a -> Bool 
is0ChildN n t = (rk t) == n

{-@ inline is2ChildN @-}
is2ChildN :: Int -> Tree a -> Bool 
is2ChildN n t = (rk t) < n && n <= (rk t) + 2


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
                         && is2ChildN n l
                         && ((notEmptyTree l) || (notEmptyTree r) || (n == 0)) -- disallow 2,2-leafs
                         && (balanced l)
                         && (balanced r)

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

{-@ singleton :: a -> {v:NEWavl | ht v == 0 && rk v == 0 && isNode1_1 v && potT v == 0 && not (isNode2_2 v)} @-}
singleton a = Tree a 0 Nil Nil

-- potential analysis for insertion
{-@ measure potT @-}
{-@ potT :: t:Wavl -> {v:Int | v >= 0} @-}
potT :: Tree a -> Int
potT Nil      = 0
potT (Tree _ n l r) 
  | rk l == rk r && rk l + 1 == n && n > 0 = 1 + potT l + potT r        -- 1,1-Node, but not leaf
  | rk l == rk r && rk l + 2 == n          = 2 + potT l + potT r        -- 2,2-Node
  | otherwise = potT l + potT r                                

{-@ measure potT2 @-}
{-@ potT2 :: t:AlmostWavl -> {v:Int | v >= 0} @-}
potT2 :: Tree a -> Int 
potT2 Nil = 0
potT2 t@(Tree _ n l r)
  | rk l + 1 == n && rk r == n              = 1 + potT l + potT r    -- 0,1-Node
  | rk r + 1 == n && rk l == n              = 1 + potT l + potT r    -- 1,0-Node
  | rk r + 1 == n && rk l + 1 == n && n > 0 = 1 + potT l + potT r    -- 1,1-Node, but not leaf
  | rk l == rk r && rk l + 2 == n           = 2 + potT l + potT r    -- 2,2-Node
  | rk l + 2 == n && rk r + 3 == n          = 2 + potT l + potT r    -- 2,3-Node
  | rk l + 3 == n && rk r + 2 == n          = 2 + potT l + potT r    -- 3,2-Node
  | otherwise = potT l + potT r

{-@ inline pot1 @-}
{-@ pot1 :: Tick (t:Wavl) -> {v:Int | v >= 0} @-}
pot1 :: Tick (Tree a) -> Int
pot1 t = potT (tval t)

{-@ inline pot12 @-}
{-@ pot12 :: Tick (t:AlmostWavl) -> {v:Int | v >= 0} @-}
pot12 :: Tick (Tree a) -> Int
pot12 t = potT2 (tval t)

{-@ type PromoteL_t = (t1:Node0_1 -> {t:EqT1 t1 | IsNode1_2 t && RkDiff t t1 1 
          && potT2 t1 -1 == potT t} ) @-}
{-@ promoteL :: PromoteL_t @-}
promoteL :: Tree a -> Tree a
promoteL (Tree a n l r) = (Tree a (n+1) l r)

{-@ type PromoteR_t = (t1:Node1_0 -> {t:EqT1 t1 | IsNode2_1 t && RkDiff t t1 1 && potT2 t1 -1 == potT t} ) @-}
{-@ promoteR :: PromoteR_t @-}
promoteR :: Tree a -> Tree a
promoteR (Tree a n l r) = (Tree a (n+1) l r)

{-- 
potT2 v + 1 == potT t ... if b, c are NIL, then potT (right t) == 0
--}
{-@ type RotateRight_t = ({t1:Node0_2 | IsNode1_2 (left t1) } 
          -> {t:EqT1 t1 | IsNode1_1 t && EqRk t1 t && (potT2 t1 + 2 == potT t || potT2 t1 + 1 == potT t) }) @-}
{-@ rotateRight :: RotateRight_t @-}
rotateRight :: Tree a -> Tree a
rotateRight (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)


{-@ type RotateLeft_t = ({t1:Node2_0 | IsNode2_1 (right t1) } 
          -> {t:EqT1 t1 | IsNode1_1 t && EqRk t1 t && (potT2 t1 + 2 == potT t || potT2 t1 + 1 == potT t) }) @-}
{-@ rotateLeft :: RotateLeft_t @-}
rotateLeft :: Tree a -> Tree a
rotateLeft t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c
{-- 
potT2 v - 1 == potT t ... if b,c are NIL, then potT (left t) == 0 &&  potT (right t) == 0 
--}
{-@ type RotateDoubleRight_t = ({t1:Node0_2 | IsNode2_1 (left t1) } 
          -> {t:EqT1 t1 | IsNode1_1 t && EqRk t1 t && (potT2 t1 - 1 == potT t || potT2 t1 + 2 == potT t || potT2 t1 + 1 == potT t)}) @-}
{-@ rotateDoubleRight :: RotateDoubleRight_t @-}
rotateDoubleRight :: Tree a -> Tree a 
rotateDoubleRight (Tree z n (Tree x m a (Tree y o b c)) d) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 

{-@ type RotateDoubleLeft_t = ({t1:Node2_0 | IsNode1_2 (right t1) } 
          -> {t:EqT1 t1 | IsNode1_1 t && EqRk t1 t && (potT2 t1 - 1 == potT t || potT2 t1 + 2 == potT t || potT2 t1 + 1 == potT t) }) @-}
{-@ rotateDoubleLeft ::  RotateDoubleLeft_t @-}
rotateDoubleLeft :: Tree a -> Tree a
rotateDoubleLeft (Tree x n a (Tree y m (Tree z o b_1 b_2) c)) = Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 

{-@ demoteL :: s:Node3_2 -> {t:NEWavl | RkDiff s t 1 && potT2 s - 2 == potT2 t } @-}
demoteL :: Tree a -> Tree a
demoteL (Tree a n l r) = Tree a (n - 1) l r

{-@ demoteR :: s:Node2_3 -> {t:NEWavl | RkDiff s t 1 && potT2 s - 2 == potT2 t } @-}
demoteR :: Tree a -> Tree a
demoteR (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteL :: {s:Node3_1 | IsNode2_2 (right s) } 
          -> {t:NEWavl | RkDiff s t 1 && potT2 s - 1 == potT2 t } @-}
doubleDemoteL :: Tree a -> Tree a
doubleDemoteL (Tree x n l (Tree y m rl rr)) = (Tree x (n-1) l (Tree x (m-1) rl rr))

{-@ doubleDemoteR :: {s:Node1_3 | IsNode2_2 (left s) } 
          -> {t:NEWavl | RkDiff s t 1 && potT2 s - 1 == potT2 t } @-}
doubleDemoteR :: Tree a -> Tree a
doubleDemoteR (Tree x n (Tree y m ll lr) r) = Tree x (n-1) (Tree y (m-1) ll lr) r 

{-- 
if Tree y is a
  leaf            -> potT2 s     == potT t
  1,1 and no leaf -> potT2 s - 1 == potT t
  2,1             -> potT2 s + 2 == potT t
--}
{-@ rotateLeftD :: {s:Node3_1 | Child1 (rk (right s)) (right (right s)) 
          && (potT (left s)) + (potT (right s)) == potT2 s } 
          -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s - 1 == potT t || potT2 s + 2 == potT t)
          } @-}
rotateLeftD t@(Tree z n l@Nil (Tree y m rl@Nil rr)) = Tree y (m+1) (Tree z 0 Nil Nil) rr
rotateLeftD t@(Tree z n l (Tree y m rl rr)) = Tree y (m+1) (Tree z (n-1) l rl) rr 

{-@ rotateRightD :: {s:Node1_3 | Child1 (rk (left s)) (left (left s))  
          && (potT (left s)) + (potT (right s)) == potT2 s} 
          -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s - 1 == potT t || potT2 s + 2 == potT t) } @-}
rotateRightD :: Tree a -> Tree a
rotateRightD (Tree x n (Tree y m ll Nil) Nil) = Tree y (m+1) ll (singleton x) -- y is 2,2-node, n-2
rotateRightD (Tree x n (Tree y m ll lr) r) = Tree y (m+1) ll (Tree x (n-1) lr r) 

{-- 
if Tree x is
  a leaf          -> potT2 s + 2 == potT t
  1,2             -> potT2 s + 3 == potT t
  2,2             -> potT2 s     == potT t
  1,1 and no leaf -> potT2 s + 3 == potT t 
--}
{-@ rotateDoubleLeftD :: {s:Node3_1 | IsNode1_2 (right s) 
          && (potT (left s)) + (potT (right s)) == potT2 s } 
          -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s + 2 == potT t || potT2 s + 3 == potT t ) } @-} 
rotateDoubleLeftD :: Tree a -> Tree a
rotateDoubleLeftD (Tree z n l (Tree y m (Tree x o rll rlr) rr)) = Tree x n (Tree z (n-2) l rll) (Tree y (n-2) rlr rr)

{-@ rotateDoubleRightD :: {s:Node1_3 | IsNode2_1 (left s) && (potT (left s)) + (potT (right s)) == potT2 s }
          -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s + 2 == potT t || potT2 s + 3 == potT t ) } @-}
rotateDoubleRightD :: Tree a -> Tree a
rotateDoubleRightD (Tree x n (Tree y m ll (Tree z o lrl lrr)) r) = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)

{-- insert x t = c is
  2,2 -> must be EqRk, since this case isn't produced from bal*, therefore -> (isNode2_2 c) -> EqRk c t
  1,2 || 2,1  -> can be either a case "after" rebalancing or be a promote step but also for a promote step
  1,1:  can have different causes, but for all cases it is true that: (rk c > 0) && isNode1_1 c -> EqRk c t
      Exception is the singleton-case: (rk == 0) && isNode1_1 c => RkDiff t c 1   
  
  from that we conclude the following clauses for 1,1 / 2,2 (refining for t): 
    (isNode2_2 t || isNode1_1 t) ==> (RkDiff t s 0) <=> 
    not (isNode2_2 t || isNode1_1 t) || (RkDiff t s 0) <=> 
    (not (isNode2_2 t) && not (isNode1_1 t)) || (RkDiff t s 0) 

    then we can say for t in insert:
     (isNode1_1 t && rk t == 0) ==> RkDiff t s 1           <=> (not (isNode1_1 t && rk t == 0)) || RkDiff t s 1
     (isNode1_1 t && rk t > 0)  ==> RkDiff t s 0           <=> (not (isNode1_1 t && rk t > 0))  || RkDiff t s 0

  And finally, I added IsWavlNode t which made it valid. The same was done to balL/R
  -> my reasoning: by bounding the case group explicitly by defining all possible cases LH is able to determine which cases are allowed and which aren't

  refinement for potential annotation clauses: 
  (RkDiff s t 1) ==> (potT (tval t') + tcost t' <= potT s)     <=> 
   not (RkDiff s t 1) || (potT (tval t') + tcost t' <= potT s) <=> 
    ((EqRk t s) || (potT (tval t') + tcost t' <= potT s)) 

  and 
  (EqRk t s) ==> (potT (tval t') + tcost t' <= potT s + 3)     <=> 
   not (EqRk t s) || (potT (tval t') + tcost t' <= potT s + 3) <=> 
   (RkDiff s t 1) || (potT (tval t') + tcost t' <= potT s + 3)

  what we know / can exclude:
  * we don't need to specify both potT and potT2 bc we know that the input and output of insert is a wavl tree, thus satisfying potT, which has the stronger constraint, i.e. compare balL/R 

clause `isNode2_2nNil t ==> EqRk t s`:
  we know that `(not (isNode2_2 s) || (EqRk t s))`should also hold for insert, since if s is a 2,2-Node then regardless of the outcome of insert in a child the rk will stay
  the same. But here we have the problem that isNode2_2 does not allow Nil values so we had to add the helper inline function isNode2_2nNil, the small standing for 'not' 

to be inserted: 
  && (not (RkDiff s (tval t') 1) || (potT2 (tval t') + tcost t' <= potT2 s))
                          && (not (EqRk (tval t') s)     || (potT2 (tval t') + tcost t' <= potT2 s + 2))
  
--}
-- {-@ insert :: (Ord a) => a -> s:Wavl -> t':{Tick ({t:NEWavl | (EqRk t s || RkDiff t s 1) 
--           && (not (isNode2_2 t) || (EqRk t s)) 
--           && ((not (isNode1_1 t && rk t > 0)) || EqRk t s) && IsWavlNode t }) 
-- --           | tcost t' >= 0   
--              && (not (RkDiff s (tval t') 1) || amortized t' s)
--              && (not (EqRk (tval t') s)     || amortized2 t' s)
--                 }  @-} -- / [rk (tval t')]
{-@ insert :: (Ord a) => a -> s:Wavl -> {t':EqT s | amortizedStmt t' s} @-} -- / [rk (tval t')]
insert :: (Ord a) => a -> Tree a -> Tick (Tree a)
insert x Nil = pure (singleton x)
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> insR
    EQ -> pure t
    where
      l' = insert x l
      r' = insert x r
      l'' = tval l'
      r'' = tval r'
      insL | rk (tval l') < n                       = undefined -- treeLW1 v n l' r -- assert (amortized2 l' l) ?? (treeL v n l' r) -- is not accepted
           | is0ChildN n l'' && rk l'' == rk r + 1 && n == 0 = assert (not (notEmptyTree l)) ?? assert (not (notEmptyTree r)) ?? 
            -- assert (1 == potT2 (Tree x n (tval l') r)) ?? 
            assert (potT t + 1 == potT l'' + tcost l' + potT r + 1) ?? -- Leaf to 0,1-Node == +1 potential case
             wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r) )
           | is0ChildN n l'' && rk l'' == rk r + 1           = assert (isNode1_1 t) ?? assert (n > 0) ??
            -- assert (potT t == potT2 (Tree x n (tval l') r)) ??
            wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r) )
              -- Tick (tcost l' + 1) (promoteL (Tree x n (tval l') r))
           | is0ChildN n l'' && isNode1_2 l'' =  assert (isNode1_2 l'') ?? undefined -- fmapRotRight rotateRight (Tick (tcost l') (Tree x n (tval l') r))
              -- assert (rk (tval (Tick (tcost l') (Tree x n (tval l') r) )) == n) ?? 
              -- assert (rk (tval (Tick (tcost l') (Tree x n (tval l') r) )) == rk (right l'') + 2) ?? 
              -- assert (rk (rotateRight (tval (Tick (tcost l') (Tree x n (tval l') r) ))) == n) ?? 
              -- assert (rk (tval (fmapRotRight rotateRight (Tick (tcost l') (Tree x n (tval l') r)))) == n) ?? 
           | is0ChildN n l'' && isNode2_1 l'' =  undefined -- fmapRotDoubleRight rotateDoubleRight (Tick (tcost l') (Tree x n (tval l') r) )
      insR | rk (tval r') < n                  = undefined -- treeRW1 v n l r' -- assert (amortized2 r' r) ??
           | is0ChildN n r'' && rk r'' == rk l + 1  = undefined -- wmapPromR promoteR (Tick (tcost r') (Tree x n l (tval r')) )
           | is0ChildN n r'' && isNode2_1 r''= undefined -- fmapRotLeft rotateLeft (Tick (tcost r') (Tree x n l (tval r')))
           | is0ChildN n r'' && isNode1_2 r''= undefined -- fmapRotDoubleLeft rotateDoubleLeft (Tick (tcost r') (Tree x n l (tval r')))

{-@ inline amortized @-}
{-@ amortized :: Tick (Wavl) -> Tick (Wavl) -> Bool @-}
amortized :: Tick (Tree a) -> Tick (Tree a) -> Bool
amortized t' s = pot1 t' + tcost t' <= pot1 s + tcost s

{-@ inline amortized1 @-}
{-@ amortized1 :: Tick (Wavl) -> Tick (Wavl) -> Bool @-}
amortized1 :: Tick (Tree a) -> Tick (Tree a) -> Bool
amortized1 t' s = pot1 t' + tcost t' <= pot1 s + tcost s + 1

{-@ inline amortized2 @-}
{-@ amortized2 :: Tick (Wavl) -> Tick (Wavl) -> Bool @-}
amortized2 :: Tick (Tree a) -> Tick (Tree a) -> Bool
amortized2 t' s = pot1 t' + tcost t' <= pot1 s + tcost s + 2

{-@ inline amortized3 @-}
{-@ amortized3 :: Tick (Wavl) -> Tick (Wavl) -> Bool @-}
amortized3 :: Tick (Tree a) -> Tick (Tree a) -> Bool
amortized3 t' s = pot1 t' + tcost t' <= pot1 s + tcost s + 3

{-@ inline amortized' @-}
{-@ amortized' :: Tick (Wavl) -> Tick (AlmostWavl) -> Bool @-}
amortized' :: Tick (Tree a) -> Tick (Tree a) -> Bool
amortized' t' s = pot1 t' + tcost t' <= pot12 s + tcost s

{-@ inline amortized2' @-}
{-@ amortized2' :: Tick (Wavl) -> Tick (AlmostWavl) -> Bool @-}
amortized2' :: Tick (Tree a) -> Tick (Tree a) -> Bool
amortized2' t' s = pot1 t' + tcost t' <= pot12 s + tcost s + 2

{-@ inline amortizedStmt @-}
{-@ amortizedStmt :: Tick (Wavl) -> Wavl -> Bool @-}
amortizedStmt :: Tick (Tree a) -> Tree a -> Bool
amortizedStmt t' s = (not (rkDiff s (tval t') 1) || amortized t' (pure s) || amortized1 t' (pure s))
                 && (not (eqRk (tval t') s)     || amortized2 t' (pure s) || amortized3 t' (pure s))

{-@ inline amortizedStmt' @-}
{-@ amortizedStmt' :: Tick (AlmostWavl) -> Tick (Wavl) -> Bool @-}
amortizedStmt' :: Tick (Tree a) -> Tick (Tree a) -> Bool
amortizedStmt' s t' = (not (rkDiff (tval s) (tval t') 1) || amortized' t' s)
                 && (not (eqRk (tval t') (tval s))     || amortized2' t' s)

{-@ inline eqRk @-}
eqRk :: Tree a -> Tree a -> Bool
eqRk v s = rk s == rk v

{-@ inline rkDiff @-}
rkDiff :: Tree a -> Tree a -> Int -> Bool
rkDiff s v d = (rk v) - (rk s) == d

{-@ inline isAlmostWavl @-}
isAlmostWavl :: Tree a -> Bool
isAlmostWavl t = not (notEmptyTree t) || (balanced (left t) && balanced (right t))

-- TRUSTED CODE, we assume that the costs are given from the child to the parent
{-@ type TreeR n l r = {v:Tick (TreeR1 n l r) | tcost r == tcost v} @-}
{-@ type TreeR1 n l r = {t:NEAlmostWavl | left t == l && right t == tval r && rk t == n } @-}
{-@ type TreeL n l r = {v:Tick (TreeL1 n l r) | tcost l == tcost v} @-}
{-@ type TreeL1 n l r = {t:NEAlmostWavl | left t == (tval l) && right t == r && rk t == n } @-}

{-@ type NodeT0_1 n l r = {v:Tick (NodeT0_1_ n l r) | tcost l == tcost v } @-}
{-@ type NodeT0_1_ n l r = {t:Node0_1 | left t == (tval l) && right t == r && rk t == n } @-}

{-@ treeR :: x:a -> n:NodeRank -> l:ChildW n -> r:Tick (ChildW n) -> v:TreeR n l r @-}
treeR :: a -> Int -> Tree a -> Tick(Tree a) -> Tick(Tree a)
treeR x n l r = Tick (tcost r) (Tree x n l (tval r))

{-@ treeL :: x:a -> n:NodeRank -> l:Tick (ChildW n) -> r:ChildW n -> v:TreeL n l r @-}
treeL :: a -> Int -> Tick(Tree a) -> Tree a -> Tick(Tree a)
treeL x n l r = Tick (tcost l) (Tree x n (tval l) r) 

-- use that one for the promoteL case
{-@ treeL1 :: x:a -> n:NodeRank -> l:Tick ({l':ChildW n | rk l' == n && notEmptyTree l'}) -> {r:ChildW n | rk r + 1 == n} -> v:NodeT0_1 n l r @-}
treeL1 :: a -> Int -> Tick(Tree a) -> Tree a -> Tick(Tree a)
treeL1 x n l r = Tick (tcost l) (Tree x n (tval l) r) 

-- {-@ treeRW :: x:a -> n:NodeRank -> l:ChildB n -> r:Tick (r':ChildB n) -> {v:Tick ({t:NEWavl | left t == l && right t == tval r && 
--           not ((notEmptyTree l) || (notEmptyTree (tval r)) || (n == 0)) || (rk t == n) }) | tcost r == tcost v } @-}
-- treeRW :: a -> Int -> Tree a -> Tick(Tree a) -> Tick(Tree a)
-- treeRW x n l r
--   | (notEmptyTree l) || (notEmptyTree (tval r)) || (n == 0) = Tick (tcost r) (Tree x n l (tval r))
--   | otherwise = Tick (tcost r) (Tree x 0 l (tval r))

-- also should hold but not necessary: potT t >= potT l + pot1 r
{-@ treeRW1 :: x:a -> n:NodeRank -> l:ChildB n -> {r:Tick (r':NEWavl) | is2ChildN n (tval r)}  
          -> {v:Tick ({t:NEWavl | left t == l && Is2Child t (tval r) && rk t == n && IsWavlNode t }) | tcost r == tcost v
           } @-}
treeRW1 :: a -> Int -> Tree a -> Tick(Tree a) -> Tick(Tree a)
treeRW1 x n l r = Tick (tcost r) (Tree x n l (tval r))

-- tried to set `rk (tval l) == rk l'` but that did
{-@ treeLW1 :: x:a -> n:NodeRank -> {l:Tick(l':NEWavl) | is2ChildN n (tval l) } -> r:ChildB n  
          -> {v:Tick ({t:NEWavl | right t == r && Is2Child t (tval l) && rk t == n && IsWavlNode t && potT t >= pot1 l + potT r}) | tcost l == tcost v
           } @-}
treeLW1 :: a -> Int -> Tick(Tree a) -> Tree a -> Tick(Tree a)
treeLW1 x n l r = Tick (tcost l) (Tree x n (tval l) r)
  -- | otherwise = Tick (tcost r) (Tree x 0 l (tval r))



{-@ wmap :: f:(t1:NEAlmostWavl -> EqT1 t1) 
          -> {s:Tick (NEAlmostWavl) | tcost s >= 0} 
          -> {t':EqT2 s | Tick (tcost s + 1) (f (tval s)) == t' } @-}
wmap :: (Tree a -> Tree a) -> Tick (Tree a) -> Tick (Tree a)
wmap f (Tick m x) = undefined -- Tick (1 + m) (f x) 

-- use only for promoteL

{- 
is valid: 

 - potT2 (tval s) -1 == potT (tval t')
 - pot1 t' + 1 == pot12 s

to prove: pot1 t' + tcost t' <= pot12 s + tcost s

              && tcost (Tick (1 + (tcost s)) (f (tval s))) == tcost s + 1 -- tcost t' = tcost s + 1
              && pot1 t' + 1 == pot12 s
              && pot12 s == potT2 (tval s)
              && pot1 t' + tcost t' <= pot12 s + tcost s -- i.e. amortized' t' s
-}
{-@ wmapPromL :: f:PromoteL_t
          -> {s:Tick (Node0_1) | tcost s >= 0} 
          -> {t':EqT2 s | Tick (tcost s + 1) (f (tval s)) == t' 
          && RkDiff (tval t') (tval s) 1 
          && tcost t' == tcost s + 1
          && pot1 t' + 1 == pot12 s
          && pot12 s == potT2 (tval s)
          && amortized' t' s
              } @-}
wmapPromL :: (Tree a -> Tree a) -> Tick (Tree a) -> Tick (Tree a)
wmapPromL f s@(Tick m x) =  Tick (1 + m) (f x)
                          -- assert (potT2 (tval s) -1 == potT (f x))  ?? 
                          -- assert (tcost (Tick (1 + m) (f x)) == tcost s + 1) ??
                          -- assert (pot1 (f x) - potT2 (tval s) == 1) ??
                          -- assert (potT (tval t') == potT2 (tval s) - 1) ??  
                          -- assert (pot1 (f x) + tcost (f x) <= pot12 s + tcost s) ?? undefined -- Tick (1 + m) (f x) 

-- use only for promoteR
{-@ wmapPromR :: f:PromoteR_t 
          -> {s:Tick (Node1_0) | tcost s >= 0} 
          -> {t':EqT2 s | Tick (tcost s + 1) (f (tval s)) == t' && RkDiff (tval t') (tval s) 1} @-}
wmapPromR :: (Tree a -> Tree a) -> Tick (Tree a) -> Tick (Tree a)
wmapPromR f (Tick m x) = undefined -- Tick (1 + m) (f x) 

{-@ fmapRotRight :: f:({t1:Node0_2 | IsNode1_2 (left t1)} -> {t2:EqT1 t1 | EqRk t2 t1}) 
          -> {s:Tick ({s':Node0_2 | IsNode1_2 (left s')}) | tcost s >= 0} 
          -> {t':EqT2 s | Tick (tcost s) (f (tval s)) == t' && EqRk (tval t') (tval s)} @-}
fmapRotRight :: (Tree a -> Tree a) -> Tick (Tree a) -> Tick (Tree a)
fmapRotRight f (Tick m x) = undefined -- Tick (m) (f x) 

{-@ fmapRotDoubleRight :: f:({t1:Node0_2 | IsNode2_1 (left t1)} -> {t2:EqT1 t1 | EqRk t2 t1}) 
          -> {s:Tick ({s':Node0_2 | IsNode2_1 (left s')}) | tcost s >= 0} 
          -> {t':EqT2 s | Tick (tcost s) (f (tval s)) == t' && EqRk (tval t') (tval s)} @-}
fmapRotDoubleRight :: (Tree a -> Tree a) -> Tick (Tree a) -> Tick (Tree a)
fmapRotDoubleRight f (Tick m x) = undefined -- Tick (m) (f x) 

{-@ fmapRotLeft :: f:({t1:Node2_0 | IsNode2_1 (right t1)} -> {t2:EqT1 t1 | EqRk t2 t1}) 
          -> {s:Tick ({s':Node2_0 | IsNode2_1 (right s')}) | tcost s >= 0} 
          -> {t':EqT2 s | Tick (tcost s) (f (tval s)) == t' && EqRk (tval t') (tval s)} @-}
fmapRotLeft :: (Tree a -> Tree a) -> Tick (Tree a) -> Tick (Tree a)
fmapRotLeft f (Tick m x) = undefined -- Tick (m) (f x) 

{-@ fmapRotDoubleLeft :: f:({t1:Node2_0 | IsNode1_2 (right t1)} -> {t2:EqT1 t1 | EqRk t2 t1}) 
          -> {s:Tick ({s':Node2_0 | IsNode1_2 (right s')}) | tcost s >= 0} 
          -> {t':EqT2 s | Tick (tcost s) (f (tval s)) == t' && EqRk (tval t') (tval s)} @-}
fmapRotDoubleLeft :: (Tree a -> Tree a) -> Tick (Tree a) -> Tick (Tree a)
fmapRotDoubleLeft f (Tick m x) = undefined -- Tick (m) (f x) 

-- {-@ fmapBalR :: f:(t1:Node2_0 -> {t2:EqT1 t1 | EqRk t2 t1}) -> {s:Tick (Node2_0) | tcost s >= 0} -> {t':EqT2 s | Tick (tcost s) (f (tval s)) == t' && EqRk (tval t') (tval s)} @-}
-- fmapBalR :: (Tree a -> Tree a) -> Tick (Tree a) -> Tick (Tree a)
-- fmapBalR f (Tick m x) = Tick (m) (f x) 

-- idWavlT :: Int -> Int -> a -> Int -> Tree a -> Tree a -> Tree a
-- idWavlT _ _ x n l r = idWavl x n l r

-- {-@ idWavlT ::  x:a -> n:NodeRank -> l':Tick({l:Wavl | is2ChildN n l})
--           -> {r:Wavl | rk r < n && n <= rk r + 2 } 
--           -> {prev:Wavl | (potT (tval l')) + tcost l' <= (potT prev) + 2 }
--           -> {t:NEWavl | potT t + tcost l' <= potT (Tree x n prev r) + 2 } @-} 
-- idWavlT :: a -> Int -> Tick (Tree a) -> Tree a -> Tree a ->  Tree a
-- idWavlT x n l r _ = idWavl x n (tval l) r

-- {-@ idWavlTR ::  x:a -> n:NodeRank -> {l:Wavl | is2ChildN n l}
--           -> r':Tick ({r:Wavl | rk r < n && n <= rk r + 2 })
--           -> {prev:Wavl | (potT (tval r')) + tcost r' <= (potT prev) + 2 }
--           -> {t:NEWavl | potT t + tcost r' <= potT (Tree x n l prev) + 2 } @-} 
-- idWavlTR :: a -> Int -> Tick (Tree a) -> Tree a -> Tree a ->  Tree a
-- idWavlTR x n l r _ = idWavl x n l (tval r)

{-
  idWavl :: check for tree 'sanity' of tuples n l r
  s. description in docs/idWavl.md
-} 
{-@ reflect idWavl @-}
{-@ idWavl :: x:a -> n:NodeRank -> {l:Wavl | is2ChildN n l} 
          -> {r:Wavl |  is2ChildN n r } 
          -> {t:NEWavl | (not (not notEmptyTree l && not notEmptyTree r) || (rk t == rk l + 1 && rk t == rk r + 1 && rk t == 0)) 
                      && ((not notEmptyTree l && not notEmptyTree r)     || (rk t == n && left t==l && right t == r)) 
                      
                      } @-}
idWavl :: a -> Int -> Tree a -> Tree a -> Tree a
idWavl x n l r
    | notEmptyTree r = idWavlR x n l r
    | notEmptyTree l = idWavlL x n l r
    | otherwise = singleton x -- not . notEmptyTree l && not . notEmptyTree r


{-@ reflect idWavlL @-}
{-@ idWavlL :: x:a -> n:NodeRank -> {l:NEWavl | is2ChildN n l} -> {r:Wavl | is2ChildN n r } 
          -> {t:NEWavl | val t == x && rk t == n && left t==l && right t == r } @-}
idWavlL :: a -> Int -> Tree a -> Tree a -> Tree a
idWavlL x n l r = Tree x n l r

{-@ reflect idWavlR @-}
{-@ idWavlR :: x:a -> n:NodeRank -> {l:Wavl | is2ChildN n l} 
          -> {r:NEWavl | rk r < n && n <= rk r + 2 } -> {t:NEWavl | rk t == n && left t==l && right t == r } @-}
idWavlR :: a -> Int -> Tree a -> Tree a -> Tree a
idWavlR x n l r = Tree x n l r

-- {-@ promoteTL :: a -> n:NodeRank -> l':Tick ({l:NEWavl | n == rk l}) 
--           -> {r:Wavl | rk (tval l') == rk r + 1 } -> {t':Tick (t:Node1_2) | tcost t' >= 0 } @-}
-- promoteTL :: a -> Int -> Tick(Tree a) -> Tree a -> Tick (Tree a)
-- promoteTL x n l r = RTick.step (tcost l + 1) . promoteL t
--   where
--     l' = tval l
--     t = RTick.step (tcost l) (pure (idAlmostWavlL x n l' r))

{-@ idAlmostWavlL :: x:a -> n:NodeRank -> {l:NEWavl | rk l <= n && n <= rk l + 2} -> {r:Wavl | rk r < n && n <= rk r + 2 } 
          -> {t:AlmostWavl | val t == x && rk t == n && left t==l && right t == r } @-}
idAlmostWavlL :: a -> Int -> Tree a -> Tree a -> Tree a
idAlmostWavlL x n l r = Tree x n l r

{-@ idAlmostWavlR :: x:a -> n:NodeRank -> {l:Wavl | is2ChildN n l } -> {r:NEWavl | rk r <= n && n <= rk r + 2} 
          -> {t:AlmostWavl | val t == x && rk t == n && left t==l && right t == r } @-}
idAlmostWavlR :: a -> Int -> Tree a -> Tree a -> Tree a
idAlmostWavlR x n l r = Tree x n l r

-- {-@ Node_0Child :: x:a -> n:NodeRank -> {l:Wavl | rk l <= n && n <= rk l + 2 } -> {r:Wavl | rk r <= n && n <= rk r + 2} 
--           -> {t:AlmostWavl | val t == x && rk t == n && left t==l && right t == r && (is0ChildN n l || is0ChildN n r)} @-}
-- Node_0Child :: a -> Int -> Tree a -> Tree a -> Tree a
-- Node_0Child x n l r = 
  

{-| 
    refinement part for l in balL (symm. for r in balR): 
        ((rk l == 0 && isNode1_1 l) || isNode2_1 l || isNode1_2 l) <=>
        not (isNode1_1 l) || not (rk l == 0) || isNode2_1 l || isNode1_2 l) <=>
        (not (isNode1_1 l) || rk l != 0 || isNode2_1 l || isNode1_2 l) <=>
        (not (isNode1_1 l) || rk l != 0 || isNode2_1 l || isNode1_2 l)

    in words: 
    I expect l to be a 0-child. For that to be true, I define the allowed cases, i.e. either it can be a 1,2-Node where the 1-Child was
    a promote case. The other case (1,1-node) happens when l was in the previous step a singleton-case (insertion of the new node into the tree).

    All other cases are not possible by the function definition, 
    i.e. a 1,1-node which isn't a product of a singleton, can only be either a product of a rotation-case 
        or 1,1-case which is in any case a Child node of 1 or greater

    Thus we don't exclude any cases and the refinement is valid. 
|-}
-- {-@ balL :: x:a -> n:NodeRank -> {l:NEWavl | Is0ChildN n l && ((isNode1_1 l && rk l == 0) || isNode2_1 l || isNode1_2 l) }
--           -> {r:Wavl | Is2ChildN n r && rk l == rk r + 2} 
--           -> {t:NEWavl | (rk t == n || rk t == n + 1) && not (isNode2_2 t) 
--             && ((not (isNode1_1 t && rk t == 0)) || rk t - n == 1) 
--             && ((not (isNode1_1 t && rk t > 0)) || rk t == n) && IsWavlNode t 
--             && (potT t <= potT2 (Tree x n l r) + 2) } @-} -- amortisiert == 2
-- balL :: a -> Int -> Tree a -> Tree a -> Tree a
-- balL x n l r | (rk (right l) + 2) == rk l =  rotateRight (Tree x n l r) 
--              | (rk (right l) + 1) == rk l =  rotateDoubleRight (Tree x n l r)
            

-- {-@ balR :: x:a -> n:NodeRank -> {l:Wavl | Is2ChildN n l } 
--           -> {r:NEWavl | Is0ChildN n r && ((isNode1_1 r && rk r == 0) || isNode2_1 r || isNode1_2 r) && rk r == rk l + 2 }
--           -> {t:NEWavl | (rk t == n || rk t == n + 1) && not (isNode2_2 t) 
--             && ((not (isNode1_1 t && rk t == 0)) || rk t - n == 1) 
--             && ((not (isNode1_1 t && rk t > 0)) || rk t == n) && IsWavlNode t 
--             && (potT t <= potT2 (Tree x n l r) + 2)}  @-} -- amortisiert == 2
-- balR :: a -> Int -> Tree a -> Tree a -> Tree a
-- balR x n l r  | (rk (left r) + 2) == rk r =  rotateLeft (Tree x n l r) 
--               | (rk (left r) + 1) == rk r =  rotateDoubleLeft (Tree x n l r) 

{-- 
(potT2 t' + 1 <= (potT2 (Tree x n (tval l) r')) + 3)
if case
  singleton    -> potT2 t' == potT2 
  no bal       -> potT2 t' == potT2 
  demote       -> potT2 s -2 == potT2 t
  doubleDemote -> potT2 s - 1 == potT2 t
  rotate       -> (potT2 s == potT t || potT2 s - 1 == potT t || potT2 s + 2 == potT t)
  rotateDouble -> (potT2 s == potT t || potT2 s + 2 == potT t || potT2 s + 3 == potT t) && ( potT2 s + 3 <= potT t) 

  ??????????? needed for demote cases:
    (
        (potT2 t' + 1 <= potT2 (Tree x n (tval l) r') + 4)
      || (potT t' + 1 <= potT2 (Tree x n (tval l) r') + 4) 
    ) 
--}
-- {-@ balLDel :: x:a -> n:NodeRank -> {l:Tick ({l':Wavl | Is3ChildN n l'}) | tcost l >= 0 } -> {r':MaybeWavlNode | Is2ChildN n r'} 
--           -> {t:Tick ({t':NEWavl | (rk t' == n || rk t' + 1 == n) 
--           && (
--             ((potT2 t' + 1 <= potT2 (Tree x n (tval l) r') + 4)) 
--           || (potT t'  + 1 <= potT2 (Tree x n (tval l) r') + 4)) 
--           })| tcost t >= 0 } @-}
-- balLDel :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
-- balLDel x _ l@(Tick _ Nil) Nil  = pure (singleton x)
-- balLDel x n l r | n <= rk l' + 2 = t
--                  | n == rk l' + 3 && rk r + 2 == n = wmap demoteL t 
--                  | n == rk l' + 3 && rk r + 1 == n && rk (left r) + 2 == rk r && (rk (right r)) + 2 == rk r = wmap doubleDemoteL t
--                  | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 1 == rk r = wmap rotateLeftD t 
--                  | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = wmap rotateDoubleLeftD t
--                     where
--                       t = RTick.step (tcost l) (pure (Tree x n l' r))
--                       l' = tval l

-- {-@ balRDel :: x:a -> n:NodeRank -> {l:MaybeWavlNode | Is2ChildN n l} -> {r:Tick ({r':Wavl | Is3ChildN n r'}) | tcost r >= 0 } 
--           -> {t: Tick ({t':NEWavl | (rk t' == n || rk t' + 1 == n) 
--           && (
--             (potT2 t' + 1 <= potT2 (Tree x n l (tval r)) + 4) 
--           || (potT t' + 1 <= potT2 (Tree x n l (tval r)) + 4)) 
--           })| tcost t >= 0 } @-}
-- balRDel :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
-- balRDel x _ Nil r@(Tick _ Nil) = RTick.step (tcost r) (pure (singleton x))
-- balRDel x n l r  | n <  rk r' + 3 = t
--                   | n == rk r' + 3 && rk l + 2 == n = wmap demoteR t 
--                   | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 2 == rk l = wmap doubleDemoteR t
--                   | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 1 == rk l = wmap rotateRightD t
--                   | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 1 == rk l = wmap rotateDoubleRightD t
--                   where 
--                     t = RTick.step (tcost r) (pure (Tree x n l r')) 
--                     r' = tval r

-- Deletion functions
-- {-@ delete :: a -> s:Wavl -> {t':Tick ({t:Wavl | ((EqRk s t) || (RkDiff s t 1)) }) | tcost t' >= 0 } @-}
-- delete :: (Ord a) => a -> Tree a -> Tick (Tree a)
-- delete _ Nil = pure Nil
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

-- {-@ merge :: a -> l:Wavl -> r:Wavl -> {v:NodeRank | WavlRankN v l r } -> {t':Tick ({t:Wavl | EqRkN v t || RkDiffN v t 1 }) | tcost t' >= 0 } @-}
-- merge :: a -> Tree a -> Tree a -> Int -> Tick (Tree a)
-- merge _ Nil Nil _ = pure Nil
-- merge _ Nil r _  = pure r
-- merge _ l Nil _  = pure l
-- merge x l r n    = balRDel y n l r'
--   where
--    (r', y)     = getMin r

-- {-@  getMin :: s:NEWavl -> ({t':Tick ({t:Wavl | (EqRk s t) || (RkDiff s t 1) }) | tcost t' >= 0 }, _) @-} 
-- getMin :: Tree a -> (Tick (Tree a), a)
-- getMin (Tree x 0 Nil Nil) = (pure Nil, x)
-- getMin (Tree x 1 Nil r@(Tree _ _ _ _)) = (pure r, x)
-- getMin (Tree x n l@(Tree _ _ _ _) r@Nil) = ((balLDel x n l' r), x')
--   where
--     (l', x')             = getMin l
-- getMin (Tree x n l@(Tree _ _ _ _) r) = ((balLDel x n l' r), x')
--   where
--     (l', x')             = getMin l

-- checker function which drops the first argument, use it with an assert to prove statements about b
{-@ reflect ?? @-}
{-@ (??) :: a -> y:b -> {v:b | v == y } @-}
(??) :: a -> b -> b
x ?? y = y

{-@ assert :: {v:Bool | v == True } -> Bool @-}
assert :: Bool -> Bool
assert _ = True
{- 
  Proof of the common potential annotation

proving the following clauses can be added to insert: 
  (not (RkDiff (tval t') s 1) || (potT (tval t') + tcost t' <= potT s))
  (not (EqRk (tval t') s)     || (potT (tval t') + tcost t' <= potT s + 3))
-}

-- {-@ maxPotTProof :: t:Wavl -> { potT t - potT (left t) - potT (right t) <= rk  } / [rk t] @-}
-- insertPotTProof :: Tree a -> Proof
-- insertPotTProof t = 

-- {-@ insertPotTProof :: x:a -> t:Wavl -> { (not (RkDiff (tval (insert x t)) t 1) || (potT (tval (insert x t)) + tcost (insert x t) <= potT t)) && 
--                                   (not (EqRk (tval (insert x t)) t)     || (potT (tval (insert x t)) + tcost (insert x t) <= potT t + 3))} @-}
-- insertPotTProof :: a -> Tree a -> Proof
-- insertPotTProof x t@Nil = trivial *** QED
-- insertPotTProof x t@(Tree y n l r) = trivial *** QED 
