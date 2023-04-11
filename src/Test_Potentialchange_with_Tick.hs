{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--bscope" @-}

module Test_Potentialchange_with_Tick where

import Prelude hiding (pure)
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.RTick as RTick

{-@ reflect singleton @-}
{-@ reflect nil @-}

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

{-@ singleton :: a -> {v:NEWavl | ht v == 0 && rk v == 0 && isNode1_1 v} @-}
singleton a = Tree a 0 Nil Nil

-- potential analysis for deletion
{-@ measure potT @-}
{-@ potT :: t:Wavl -> Int @-}
potT :: Tree a -> Int
potT Nil      = 0
potT (Tree _ n l r) 
  | rk l == rk r && rk l + 1 == n = 1 + potT l + potT r        -- 1,1-Node
  | otherwise = potT l + potT r                                -- 2,*-Nodes

{-@ measure potT2 @-}
{-@ potT2 :: t:AlmostWavl -> Int @-}
potT2 :: Tree a -> Int 
potT2 t@Nil = 0
potT2 t@(Tree _ n l r)
  | rk l + 1 == n && rk r == n     = 1 + potT l + potT r    -- 0,1-Node
  | rk r + 1 == n && rk l == n     = 1 + potT l + potT r    -- 1,0-Node
  | rk r + 1 == n && rk l + 1 == n = 1 + potT l + potT r    -- 1,1-Node
  | otherwise = potT l + potT r

{-@ promoteL :: s:Node0_1 -> {t:Node1_2 | RkDiff t s 1 && potT2 s == potT t + 1 } @-}
promoteL :: Tree a -> Tree a
promoteL (Tree a n l r) = (Tree a (n+1) l r)

{-@ promoteR :: s:Node1_0 -> {t:Node2_1 | RkDiff t s 1 && potT2 s == potT t + 1 } @-}
promoteR :: Tree a -> Tree a
promoteR (Tree a n l r) = (Tree a (n+1) l r)

-- {-@ rotateRight :: {v:Node0_2 | IsNode1_2 (left v) && potT (left v) + potT (right v) == potT2 v } 
--           -> {t:NEWavl | EqRk v t && (potT2 v <= potT2 t)} @-}
-- {-@ rotateRight :: {v:Node0_2 | IsNode1_2 (left v) } 
--           -> {t:NEWavl | EqRk v t } @-}
{-@ rotateRight :: {v:Node0_2 | IsNode1_2 (left v) } -> {t:Node1_1 | EqRk v t && potT2 v + 2 == potT t } @-}
rotateRight :: Tree a -> Tree a
rotateRight (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)

{-@ rotateDoubleRight :: {v:Node0_2 | IsNode2_1 (left v) } -> {t:Node1_1 | EqRk v t && (potT2 v + 2 == potT t || potT2 v + 1 == potT t)} @-}
rotateDoubleRight :: Tree a -> Tree a 
rotateDoubleRight (Tree z n (Tree x m a (Tree y o b c)) d) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 

{-@ rotateLeft :: {v:Node2_0 | IsNode2_1 (right v) } -> {t:Node1_1 | EqRk v t && potT2 v + 2 == potT t} @-}
rotateLeft :: Tree a -> Tree a
rotateLeft t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c

{-@ rotateDoubleLeft :: {v:Node2_0 | IsNode1_2 (right v) } 
          -> {t:Node1_1 | EqRk v t && (potT2 v + 2 == potT t || potT2 v + 1 == potT t)} @-}
rotateDoubleLeft :: Tree a -> Tree a
rotateDoubleLeft (Tree x n a (Tree y m (Tree z o b_1 b_2) c)) = Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 

{-@ demoteL' :: s:Node3_2 -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t } @-}
demoteL' :: Tree a -> Tree a
demoteL' (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteL' :: {s:Node3_1 | IsNode2_2 (right s) } -> {t:NEWavl | RkDiff s t 1 && potT2 s + 1 == potT2 t } @-}
doubleDemoteL' :: Tree a -> Tree a
doubleDemoteL' (Tree x n l (Tree y m rl rr)) = (Tree x (n-1) l (Tree x (m-1) rl rr))

{-@ rotateLeftD' :: {s:Node3_1 | Child1 (rk (right s)) (right (right s)) 
          && (potT (left s)) + (potT (right s)) == potT2 s} 
          -> {t:NEWavl | EqRk s t && (potT2 s - 1 == potT t || potT2 s == potT t || potT2 s + 1 == potT t) } @-} -- potT2 s - 1 <= potT t && potT2 s >= potT t
rotateLeftD' t@(Tree z n l@Nil (Tree y m rl@Nil rr)) = Tree y (m+1) (Tree z 0 Nil Nil) rr
rotateLeftD' t@(Tree z n l (Tree y m rl rr)) = Tree y (m+1) (Tree z (n-1) l rl) rr 

{-@ rotateDoubleLeftD' :: {s:Node3_1 | IsNode1_2 (right s) 
          && (potT (left s)) + (potT (right s)) == potT2 s } 
          -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s + 1 == potT t ) } @-} 
rotateDoubleLeftD' :: Tree a -> Tree a
rotateDoubleLeftD' (Tree z n l (Tree y m (Tree x o rll rlr) rr)) = Tree x n (Tree z (n-2) l rll) (Tree y (n-2) rlr rr)

{-@ demoteR' :: s:Node2_3 -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t } @-}
demoteR' :: Tree a -> Tree a
demoteR' (Tree a n l r) = Tree a (n - 1) l r

{-@ doubleDemoteR' :: {s:Node1_3 | IsNode2_2 (left s) } 
          -> {t:NEWavl | RkDiff s t 1 && potT2 s + 1 == potT2 t } @-}
doubleDemoteR' :: Tree a -> Tree a
doubleDemoteR' (Tree x n (Tree y m ll lr) r) = Tree x (n-1) (Tree y (m-1) ll lr) r 

{-@ rotateRightD' :: {s:Node1_3 | Child1 (rk (left s)) (left (left s))  
          && (potT (left s)) + (potT (right s)) == potT2 s} 
          -> {t:NEWavl | EqRk s t && (potT2 s - 1 == potT t || potT2 s == potT t || potT2 s + 1 == potT t) } @-}
rotateRightD' :: Tree a -> Tree a
rotateRightD' (Tree x n (Tree y m ll Nil) Nil) = Tree y (m+1) ll (singleton x)
rotateRightD' (Tree x n (Tree y m ll lr) r) = Tree y (m+1) ll (Tree x (n-1) lr r) 

{-@ rotateDoubleRightD' :: {s:Node1_3 | IsNode2_1 (left s) && (potT (left s)) + (potT (right s)) == potT2 s }
          -> {t:NEWavl | EqRk s t && (potT2 s == potT t || potT2 s + 1 == potT t ) } @-}
rotateDoubleRightD' :: Tree a -> Tree a
rotateDoubleRightD' (Tree x n (Tree y m ll (Tree z o lrl lrr)) r) = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)

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


is0ChildN :: Int -> Tree a -> Bool 
is0ChildN n t = (rk t) == n

-- && (potT t + (tcost t') <= potT s + 5
-- && ((IsNode1_1 t && rk t == 0) || IsNode2_1 t || IsNode1_2 t) 

{- insert x t = c (child) ist
  2,2 -> kann direkt übergeben werden, da rk c < n sein muss -> (isNode2_2 c && rk c < n)
  1,2 || 2,1  -> ((isNode1_2 c || isNode2_1 c)
  1,1:  kann verschiedenes sein, aber unter allen Bedingungen gilt: (rk c < n) && isNode1_1 c 
      Ausnahme singleton:    
  
  daraus ergibt sich die folgende Klausel für 1,1 / 2,2 (im Refinement für t): 
    (isNode2_2 t || isNode1_1 t) ==> (RkDiff t s 0) <=> 
    not (isNode2_2 t || isNode1_1 t) || (RkDiff t s 0) <=> 
    (not (isNode2_2 t) && not (isNode1_1 t)) || (RkDiff t s 0) 

    refinement part for l : 
        ((rk l == 0 <=> isNode1_1 l) || isNode2_1 l || isNode1_2 l) <=>
        (not (isNode1_1 l && rk l == 0) || isNode2_1 l || isNode1_2 l) <=>
        ((not (isNode1_1 l) || rk l != 0) || isNode2_1 l || isNode1_2 l) <=>
        (not (isNode1_1 l) || rk l != 0 || isNode2_1 l || isNode1_2 l) <=>
    
    &&  

        not (isNode2_2 t) 

     ... but this can be implizit, since it has to be either 1,1 or 1,2 in the first place 

     this is only valid for singleton: (not (isNode1_1 t) || (rk t == 0))

    then we can say for t:
     (isNode1_1 t && rk t == 0) ==> RkDiff t s 1           <=> (not (isNode1_1 t && rk t == 0)) || RkDiff t s 1
     (isNode1_1 t && rk t > 0)  ==> RkDiff t s 0           <=> (not (isNode1_1 t && rk t > 0))  || RkDiff t s 0

  And finally, I added IsWavlNode t which made it valid, i.e. the same was done to balL/R

  Exceptions for these rule are: 
  * when singleton is called, a 1,1-node is returned and RkDiff is 1
  * when a 2,2-node is returned, it has to be RkDiff 0 since it could only be returned from the `rk l' < n` case
-}
{-@ insert :: (Ord a) => a -> s:Wavl -> t':{Tick ({t:NEWavl | (EqRk t s || RkDiff t s 1) 
          && (not (isNode2_2 t) || (EqRk t s)) 
          && ((not (isNode1_1 t && rk t > 0)) || EqRk t s) && IsWavlNode t }) 
          | tcost t' >= 0  } @-}  -- && (potT (tval t') + tcost t' <= potT s + 5)
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
      insR | rk r'' < n  = RTick.step (tcost r') (pure (Tree v n l r''))
           | rk r'' == n = RTick.step (tcost r' + 1) (pure (balR v n l r''))

{-@ balL :: x:a -> n:NodeRank -> {l:NEWavl | Is0ChildN n l && ((isNode1_1 l && rk l == 0) || isNode2_1 l || isNode1_2 l) }
          -> {r:Wavl | Is2ChildN n r} 
          -> {t:NEWavl | (rk t == n || rk t == n + 1) && not (isNode2_2 t) 
            && ((not (isNode1_1 t && rk t == 0)) || rk t - n == 1) 
            && ((not (isNode1_1 t && rk t > 0)) || rk t == n) && IsWavlNode t 
            && (potT t + 1 <= potT2 (Tree x n l r) + 3) } @-} -- tcost == 1, amortisiert == 2
balL :: a -> Int -> Tree a -> Tree a -> Tree a
balL x n l r | rk l == rk r + 1 =  promoteL t
             | rk l == rk r + 2 && (rk (right l) + 2) == rk l =  rotateRight t 
             | rk l == rk r + 2 && (rk (right l) + 1) == rk l =  rotateDoubleRight t 
              where 
                t = Tree x n l r

{-@ balR :: x:a -> n:NodeRank -> {l:Wavl | Is2ChildN n l } 
          -> {r:NEWavl | Is0ChildN n r && ((isNode1_1 r && rk r == 0) || isNode2_1 r || isNode1_2 r)}
          -> {t:NEWavl | (rk t == n || rk t == n + 1) && not (isNode2_2 t) 
            && ((not (isNode1_1 t && rk t == 0)) || rk t - n == 1) 
            && ((not (isNode1_1 t && rk t > 0)) || rk t == n) && IsWavlNode t 
            && (potT t + 1 <= potT2 (Tree x n l r) + 3)}  @-}
balR :: a -> Int -> Tree a -> Tree a -> Tree a
balR x n l r  | rk r == rk l + 1 =  promoteR t
              | rk r == rk l + 2 && (rk (left r) + 2) == rk r =  rotateLeft t 
              | rk r == rk l + 2 && (rk (left r) + 1) == rk r =  rotateDoubleLeft t 
               where 
                 t = Tree x n l r

{-@ idWavl :: {v:NEWavl | Is1Child v (left v) } -> {t:NEWavl | rk v == rk t} @-}
idWavl :: Tree a -> Tree a
idWavl t = t

-- doesn't work, l' /r' are not recognized to be the concrete type in spite of being recognized when unwrapped
-- {-@ insert :: (Ord a) => a -> s:Wavl -> t':{Tick ({t:NEWavl | (EqRk t s || RkDiff t s 1) 
--           && (not (isNode2_2 t) || (EqRk t s)) 
--           && ((not (isNode1_1 t && rk t > 0)) || EqRk t s) && IsWavlNode t }) 
--           | tcost t' >= 0  } @-}  -- && (potT (tval t') + tcost t' <= potT s + 5)
-- insert :: (Ord a) => a -> Tree a -> Tick (Tree a)
-- insert x Nil = pure (singleton x)
-- insert x t@(Tree v n l r) = case compare x v of
--     LT -> insL
--     GT -> insR
--     EQ -> pure t
--     where 
--       l' = insert x l
--       r' = insert x r
--       l'' = tval l'
--       r'' = tval r'
--       insL | rk l'' < n  = RTick.step (tcost l') (pure (Tree v n l'' r))
--            | rk (tval l') == n = balL v n l' r
--       insR | rk r'' < n  = RTick.step (tcost r') (pure (Tree v n l r''))
--            | rk r'' == n = balR v n l r'

-- {-@ balL :: x:a -> n:NodeRank -> {l':Tick ({l:NEWavl | Is0ChildN n l && ((isNode1_1 l && rk l == 0) || isNode2_1 l || isNode1_2 l) }) | tcost l' >= 0} 
--           -> {r:Wavl | Is2ChildN n r} 
--           -> {t':Tick ({t:NEWavl | (rk t == n || rk t == n + 1) && not (isNode2_2 t) 
--             && ((not (isNode1_1 t && rk t == 0)) || rk t - n == 1) 
--             && ((not (isNode1_1 t && rk t > 0)) || rk t == n) && IsWavlNode t 
--             && (potT t + tcost t' - tcost l' <= potT2 (Tree x n (tval l') r) + 3) }) 
--             | tcost t' >= 0}  @-}
-- balL :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
-- balL x n l r | rk l' == rk r + 1 = RTick.wmap promoteL t
--              | rk l' == rk r + 2 && (rk (right l') + 2) == rk l' = RTick.wmap rotateRight t 
--              | rk l' == rk r + 2 && (rk (right l') + 1) == rk l' = RTick.wmap rotateDoubleRight t 
--               where 
--                 t = RTick.step (tcost l) (pure (Tree x n l' r))
--                 l' = tval l

-- {-@ balR :: x:a -> n:NodeRank -> {l:Wavl | Is2ChildN n l } 
--           -> {r':Tick ({r:NEWavl | Is0ChildN n r && ((isNode1_1 r && rk r == 0) || isNode2_1 r || isNode1_2 r)}) | tcost r' >= 0 }
--           -> {t':Tick ({t:NEWavl | (rk t == n || rk t == n + 1) && not (isNode2_2 t) 
--             && ((not (isNode1_1 t && rk t == 0)) || rk t - n == 1) 
--             && ((not (isNode1_1 t && rk t > 0)) || rk t == n) && IsWavlNode t 
--             && (potT t + tcost t' - tcost r' <= potT2 (Tree x n l (tval r')) + 3 )})
--             | tcost t' >= 0 }  @-}
-- balR :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
-- balR x n l r  | rk r' == rk l + 1 = RTick.wmap promoteR t
--               | rk r' == rk l + 2 && (rk (left r') + 2) == rk r' = RTick.wmap rotateLeft t 
--               | rk r' == rk l + 2 && (rk (left r') + 1) == rk r' = RTick.wmap rotateDoubleLeft t 
--                where 
--                  t = RTick.step (tcost r) (pure (Tree x n l r'))
--                  r' = tval r

