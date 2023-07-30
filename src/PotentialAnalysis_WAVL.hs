{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--bscope" @-}

module PotentialAnalysis_WAVL where

import Prelude hiding (pure)
import Language.Haskell.Liquid.RTick as RTick
import Language.Haskell.Liquid.ProofCombinators 

{-@ reflect singleton @-}
{-@ reflect nil @-}

{-@ reflect promoteL @-}
{-@ reflect promoteR @-}
{-@ reflect rotateDoubleLeft @-}
{-@ reflect rotateDoubleRight @-}
{-@ reflect rotateLeft @-}
{-@ reflect rotateRight @-}

{-@ reflect balL @-}
{-@ reflect balR @-}
-- {-@ reflect insert @-}


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

{-@ type Node0_1 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (left v)  && (RkDiff v (left v) 0 ) && (RkDiff v (right v) 1) && rk v >= 0 } @-}
{-@ type Node1_0 = { v:AlmostWavl | notEmptyTree v && notEmptyTree (right v) && (RkDiff v (left v) 1 ) && (RkDiff v (right v) 0) && rk v >= 0 } @-}

{-@ type Node1_1 = { v:NEWavl | IsNode1_1 v } @-}
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
                            && rk L < N && N <= rk L + 2 
                            && ((notEmptyTree l) || (notEmptyTree r) || (v == 0)) @-}
{-@ predicate WavlRankL N L R = rk R < N && N <= rk R + 2
                            && rk L < N && N <= rk L + 3 @-}
{-@ predicate WavlRankR N L R = rk R < N && N <= rk R + 3
                            && rk L < N && N <= rk L + 2 @-}

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

{-@ inline is0ChildN @-}
is0ChildN :: Int -> Tree a -> Bool 
is0ChildN n t = (rk t) == n

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

{-@ measure ht @-}
{-@ ht :: Tree a -> Rank @-}
ht              :: Tree a -> Int
ht Nil          = (-1)
ht (Tree x n l r) = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

{-@ measure empty @-}
empty :: Tree a -> Bool
empty Nil = True
empty _ = False

{-@ singleton :: a -> {v:NEWavl | ht v == 0 && rk v == 0 && isNode1_1 v && potT v == 0} @-}
singleton a = Tree a 0 Nil Nil

-- potential analysis for insertion
{-@ measure potT @-}
{-@ potT :: t:Wavl -> Int @-}
potT :: Tree a -> Int
potT Nil      = 0
potT (Tree _ n l r) 
  | rk l == rk r && rk l + 1 == n && n > 0 = 1 + potT l + potT r        -- 1,1-Node, but not leaf
  | rk l == rk r && rk l + 2 == n          = 2 + potT l + potT r        -- 2,2-Node
  | otherwise = potT l + potT r                                

{-@ measure potT2 @-}
{-@ potT2 :: t:AlmostWavl -> Int @-}
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

{-@ promoteL :: s:Node0_1 -> {t:Node1_2 | RkDiff t s 1 && potT2 s -1 == potT t } @-}
promoteL :: Tree a -> Tree a
promoteL (Tree a n l r) = (Tree a (n+1) l r)

{-@ promoteR :: s:Node1_0 -> {t:Node2_1 | RkDiff t s 1 && potT2 s -1 == potT t } @-}
promoteR :: Tree a -> Tree a
promoteR (Tree a n l r) = (Tree a (n+1) l r)

{-- 
potT2 v + 1 == potT t ... if b, c are NIL, then potT (right t) == 0
--}
{-@ rotateRight :: {v:Node0_2 | IsNode1_2 (left v) } 
          -> {t:Node1_1 | EqRk v t && (potT2 v + 2 == potT t || potT2 v + 1 == potT t) } @-}
rotateRight :: Tree a -> Tree a
rotateRight (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)

{-@ rotateLeft :: {v:Node2_0 | IsNode2_1 (right v) } 
          -> {t:Node1_1 | EqRk v t && (potT2 v + 2 == potT t || potT2 v + 1 == potT t) } @-}
rotateLeft :: Tree a -> Tree a
rotateLeft t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c
{-- 
potT2 v - 1 == potT t ... if b,c are NIL, then potT (left t) == 0 &&  potT (right t) == 0 
--}
{-@ rotateDoubleRight :: {v:Node0_2 | IsNode2_1 (left v) } 
          -> {t:Node1_1 | EqRk v t && (potT2 v - 1 == potT t || potT2 v + 2 == potT t || potT2 v + 1 == potT t)} @-}
rotateDoubleRight :: Tree a -> Tree a 
rotateDoubleRight (Tree z n (Tree x m a (Tree y o b c)) d) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 

{-@ rotateDoubleLeft :: {v:Node2_0 | IsNode1_2 (right v) } 
          -> {t:Node1_1 | EqRk v t && (potT2 v - 1 == potT t || potT2 v + 2 == potT t || potT2 v + 1 == potT t) } @-}
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

{- insert x t = c is
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
  * 
-}
{-@ insert :: (Ord a) => a -> s:Wavl -> t':{Tick ({t:NEWavl | (EqRk t s || RkDiff t s 1) 
          && (not (isNode2_2 t) || (EqRk t s)) 
          && ((not (isNode1_1 t && rk t > 0)) || EqRk t s) && IsWavlNode t }) 
          | tcost t' >= 0 
          }  @-} -- / [rk (tval t')]
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
      insL | rk l'' < n  = RTick.step (tcost l') (pure (Tree v n l'' r))
           | rk l'' == n = RTick.step (tcost l' + 1) (pure (balL v n l'' r)) 
           | otherwise   = RTick.step (tcost l') (pure (Tree v n l'' r))
      insR | rk r'' < n  = RTick.step (tcost r') (pure (Tree v n l r''))
           | rk r'' == n = RTick.step (tcost r' + 1) (pure (balR v n l r''))
           | otherwise   = RTick.step (tcost l') (pure (Tree v n l r''))

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
{-@ balL :: x:a -> n:NodeRank -> {l:NEWavl | Is0ChildN n l && ((isNode1_1 l && rk l == 0) || isNode2_1 l || isNode1_2 l) }
          -> {r:Wavl | Is2ChildN n r} 
          -> {t:NEWavl | (rk t == n || rk t == n + 1) && not (isNode2_2 t) 
            && ((not (isNode1_1 t && rk t == 0)) || rk t - n == 1) 
            && ((not (isNode1_1 t && rk t > 0)) || rk t == n) && IsWavlNode t 
            && (potT t + 1 <= potT2 (Tree x n l r) + 3) } @-} -- tcost == 1, amortisiert == 2
balL :: a -> Int -> Tree a -> Tree a -> Tree a
balL x n l r | rk l == rk r + 1 =  promoteL (Tree x n l r)
             | rk l == rk r + 2 && (rk (right l) + 2) == rk l =  rotateRight (Tree x n l r) 
             | rk l == rk r + 2 && (rk (right l) + 1) == rk l =  rotateDoubleRight (Tree x n l r)
             | otherwise = Tree x n l r

{-@ balR :: x:a -> n:NodeRank -> {l:Wavl | Is2ChildN n l } 
          -> {r:NEWavl | Is0ChildN n r && ((isNode1_1 r && rk r == 0) || isNode2_1 r || isNode1_2 r)}
          -> {t:NEWavl | (rk t == n || rk t == n + 1) && not (isNode2_2 t) 
            && ((not (isNode1_1 t && rk t == 0)) || rk t - n == 1) 
            && ((not (isNode1_1 t && rk t > 0)) || rk t == n) && IsWavlNode t 
            && (potT t + 1 <= potT2 (Tree x n l r) + 3)}  @-} -- tcost == 1, amortisiert == 2
balR :: a -> Int -> Tree a -> Tree a -> Tree a
balR x n l r  | rk r == rk l + 1 =  promoteR (Tree x n l r)
              | rk r == rk l + 2 && (rk (left r) + 2) == rk r =  rotateLeft (Tree x n l r) 
              | rk r == rk l + 2 && (rk (left r) + 1) == rk r =  rotateDoubleLeft (Tree x n l r) 
              | otherwise = (Tree x n l r) 

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
{-@ balLDel :: x:a -> n:NodeRank -> {l:Tick ({l':Wavl | Is3ChildN n l'}) | tcost l >= 0 } -> {r':MaybeWavlNode | Is2ChildN n r'} 
          -> {t:Tick ({t':NEWavl | (rk t' == n || rk t' + 1 == n) 
          && (
            ((potT2 t' + 1 <= potT2 (Tree x n (tval l) r') + 4) && (balanced t')) 
          || (potT t'  + 1 <= potT2 (Tree x n (tval l) r') + 4)) 
          })| tcost t >= 0 } @-}
balLDel :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
balLDel x _ l@(Tick _ Nil) Nil  = pure (singleton x)
balLDel x n l r | n <= rk l' + 2 = t
                 | n == rk l' + 3 && rk r + 2 == n = RTick.wmap demoteL t 
                 | n == rk l' + 3 && rk r + 1 == n && rk (left r) + 2 == rk r && (rk (right r)) + 2 == rk r = RTick.wmap doubleDemoteL t
                 | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 1 == rk r = RTick.wmap rotateLeftD t 
                 | n == rk l' + 3 && rk r + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = RTick.wmap rotateDoubleLeftD t
                    where
                      t = RTick.step (tcost l) (pure (Tree x n l' r))
                      l' = tval l

{-@ balRDel :: x:a -> n:NodeRank -> {l:MaybeWavlNode | Is2ChildN n l} -> {r:Tick ({r':Wavl | Is3ChildN n r'}) | tcost r >= 0 } 
          -> {t: Tick ({t':NEWavl | (rk t' == n || rk t' + 1 == n) 
          && (
            (potT2 t' + 1 <= potT2 (Tree x n l (tval r)) + 4) 
          || (potT t' + 1 <= potT2 (Tree x n l (tval r)) + 4)) 
          })| tcost t >= 0 } @-}
balRDel :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
balRDel x _ Nil r@(Tick _ Nil) = RTick.step (tcost r) (pure (singleton x))
balRDel x n l r  | n <  rk r' + 3 = t
                  | n == rk r' + 3 && rk l + 2 == n = RTick.wmap demoteR t 
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 2 == rk l = RTick.wmap doubleDemoteR t
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 1 == rk l = RTick.wmap rotateRightD t
                  | n == rk r' + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 1 == rk l = RTick.wmap rotateDoubleRightD t
                  where 
                    t = RTick.step (tcost r) (pure (Tree x n l r')) 
                    r' = tval r

-- Deletion functions
{-@ delete :: a -> s:Wavl -> {t':Tick ({t:Wavl | ((EqRk s t) || (RkDiff s t 1)) }) | tcost t' >= 0 } @-}
delete :: (Ord a) => a -> Tree a -> Tick (Tree a)
delete _ Nil = pure Nil
delete y (Tree x n l@Nil r@Nil)
  | y < x     = balLDel x n l' r
  | x < y     = balRDel x n l r'
  | otherwise = merge y l r n 
    where
      l' = delete x l
      r' = delete x r
delete y (Tree x n l@Nil r@(Tree _ _ _ _))
  | y < x     = balLDel x n l' r
  | x < y     = balRDel x n l r'
  | otherwise = merge y l r n 
    where
      l' = delete x l
      r' = delete x r
delete y (Tree x n l@(Tree _ _ _ _) r@Nil)
  | y < x     = balLDel x n l' r
  | x < y     = balRDel x n l r'
  | otherwise = merge y l r n 
    where
      l' = delete x l
      r' = delete x r
delete y (Tree x n l@(Tree _ _ _ _) r@(Tree _ _ _ _))
  | y < x     = balLDel x n l' r
  | x < y     = balRDel x n l r'
  | otherwise = merge y l r n 
    where
      l' = delete x l
      r' = delete x r

{-@ merge :: a -> l:Wavl -> r:Wavl -> {v:NodeRank | WavlRankN v l r } -> {t':Tick ({t:Wavl | EqRkN v t || RkDiffN v t 1 }) | tcost t' >= 0 } @-}
merge :: a -> Tree a -> Tree a -> Int -> Tick (Tree a)
merge _ Nil Nil _ = pure Nil
merge _ Nil r _  = pure r
merge _ l Nil _  = pure l
merge x l r n    = balRDel y n l r'
  where
   (r', y)     = getMin r

{-@  getMin :: s:NEWavl -> ({t':Tick ({t:Wavl | (EqRk s t) || (RkDiff s t 1) }) | tcost t' >= 0 }, _) @-} 
getMin :: Tree a -> (Tick (Tree a), a)
getMin (Tree x 0 Nil Nil) = (pure Nil, x)
getMin (Tree x 1 Nil r@(Tree _ _ _ _)) = (pure r, x)
getMin (Tree x n l@(Tree _ _ _ _) r@Nil) = ((balLDel x n l' r), x')
  where
    (l', x')             = getMin l
getMin (Tree x n l@(Tree _ _ _ _) r) = ((balLDel x n l' r), x')
  where
    (l', x')             = getMin l

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
