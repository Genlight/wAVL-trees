{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--bscope" @-}
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--diff" @-}

module PotentialAnalysis_WAVL_v2 where

import Prelude hiding (pure, wmap, fmap)
import Language.Haskell.Liquid.ProofCombinators 
import Language.Haskell.Liquid.RTick as RTick

-- Basic functions
{-@ data Tree [rk] a = Nil | Tree { val :: a, 
                                    rd :: {v:Int | v >= 0}, 
                                    left :: ChildT a rd,
                                    right :: ChildT a rd } @-} 
data Tree a = Nil | Tree { val :: a, rd :: Int, left :: (Tree a), right :: (Tree a)} deriving Show

{-@ type ChildT a K = {v:Tree a | rk v < K && K <= rk v + 2 } @-}

{-@ type Wavl = {v:Tree a | structLemma v } @-}
{-@ type NEWavl = {v:Wavl | not (empty v) } @-}

{-@ measure structLemma @-}
structLemma :: Tree a -> Bool
structLemma Nil = True
structLemma t@(Tree _ n l r) = isWavlNode t && structLemma l && structLemma r 

-- potential analysis for deletion
{-@ measure potT @-}
{-@ potT :: t:Wavl -> Nat @-}
potT :: Tree a -> Int
potT Nil      = 0
potT t@(Tree _ n l r) 
  | isNode1_1 t && n > 0 = 1 + potT l + potT r        -- 1,1-Node, but not leaf
  | child2 t l && child2 t r = 2 + potT l + potT r    -- 2,2-Node
  | otherwise = potT l + potT r                       -- 1,*-Nodes

{-@ inline pot @-}
{-@ pot :: Tick (Wavl) -> Nat @-}
pot :: Tick (Tree a) -> Int
pot t = potT (tval t)

{-@ measure rk @-}
{-@ rk :: t:Tree a -> {v:Int | (empty t => v == (-1)) && ( not (empty t) => v >= 0)} @-}
rk :: Tree a -> Int
rk Nil =  -1
rk t@(Tree _ n _ _) = n

{-@ leaf :: a -> {v:NEWavl | rk v == 0 && isNode1_1 v && potT v == potT (left v) + potT (right v) && potT v == 0 } @-}  --  && not (isNode2_2 v)
leaf a = Tree a 0 Nil Nil

{-@ measure empty @-}
empty :: Tree a -> Bool
empty Nil = True
empty _ = False

{-@ inline rkDiff @-}
rkDiff :: Tree a -> Tree a -> Int -> Bool
rkDiff t s n = rk t - rk s  == n

{-@ insert :: (Ord a) => a -> s:Wavl -> {t':Tick ({t:NEWavl | ((rkDiff t s 1) || (rkDiff t s 0)) 
                    && ((rkDiff t s 1 && rk s >= 0) => (isNode1_2 t || isNode2_1 t)) } )|
                    (rk s >= 0 => amortized1 s t' ) &&
                    (rk s ==(-1) => amortized s t' ) } @-}
insert :: (Ord a) => a -> Tree a -> Tick (Tree a)
insert x Nil = pure (leaf x)
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> insR
    EQ -> pure t
    where
        l' = insert x l
        r' = insert x r
        l'' = tval l'
        r'' = tval r'
        insL 
            | rk (tval l') < rk t = undefined -- inTreeL t l'
            | isNode1_1 t = assert (rk (tval l') == rk t) ?? undefined -- wmapPromoteL t l'
            | isNode1_2 t && isNode1_2 l'' = undefined -- fmapRotateRight t l'
            | isNode1_2 t && isNode2_1 l'' = undefined -- rotateDoubleRight t l'
        insR 
            | rk r'' < rk t = undefined -- Tree x n l r'
            | isNode1_1 t = undefined -- promoteR t r'
            | isNode2_1 t && isNode2_1 r'' = undefined -- rotateLeft t r'
            | isNode2_1 t && isNode1_2 r'' = undefined -- rotateDoubleLeft t r'


{- 
{-@ delete :: (Ord a) => a -> s:Wavl -> {t:Wavl | ((rkDiff s t 0) || (rkDiff s t 1))} @-}
delete::  (Ord a) => a -> Tree a -> Tree a
delete _ Nil = Nil
delete y t@(Tree x n l r) = case compare x y of
    LT -> delL t l'
    GT -> delR t r'
    EQ -> merge t 
    where
        l' = delete x l
        r' = delete x r

{-@ merge :: s:NEWavl -> {t:Wavl | ((rkDiff s t 0) || (rkDiff s t 1))} @-}
merge :: Tree a -> Tree a
merge t@(Tree _ n Nil Nil) = Nil
merge t@(Tree _ n Nil r) = r
merge t@(Tree _ n l Nil) = l
merge t@(Tree _ n l r)   = delR (Tree x n l r) r'
    where 
        (r', x)     = getMin r

{-@ delR :: t:NEWavl -> {r:Wavl | ((rkDiff (right t) r 0) || (rkDiff (right t) r 1))} -> {v:NEWavl | ((rkDiff t v 0) || (rkDiff t v 1))} @-}
delR t@(Tree x n Nil _) r = treeR t r
delR t@(Tree x n l@(Tree _ _ ll lr) _) r 
        | rk t <= rk r + 2 = treeR t r
        | child3 t r && child2 t l = demoteR t r
        | child3 t r && child2 l lr && child2 l ll = doubleDemoteR t r
        | child3 t r && child1 l ll = rotateRightD t r
        | child3 t r && child1 l lr = rotateDoubleRightD t r

{-@ delL :: t:NEWavl -> {l:Wavl | ((rkDiff (left t) l 0) || (rkDiff (left t) l 1))} -> {v:NEWavl | ((rkDiff t v 0) || (rkDiff t v 1))} @-}
delL t@(Tree x n _ r@Nil) l = treeL t l
delL t@(Tree x n _ r@(Tree _ _ rl rr)) l 
        | n <= rk l + 2 = treeL t l
        | child3 t l && child2 t r = demoteL t l
        | child3 t l && child2 r rr && child2 r rl = doubleDemoteL t l
        | child3 t l && child1 r rr = rotateLeftD t l
        | child3 t l && child1 r rl = rotateDoubleLeftD t l

{-@ treeL :: t:NEWavl -> {l:Wavl | ((rkDiff (left t) l 0) || (rkDiff (left t) l 1)) && rk t <= rk l + 2} 
                    -> {v:NEWavl | (rkDiff t v 0) || (rkDiff t v 1)} @-} 
treeL :: Tree a -> Tree a -> Tree a
treeL (Tree x 1 (Tree _ 0 Nil Nil) Nil) Nil = leaf x
treeL (Tree x n _ r) l = Tree x n l r 

{-@ treeR :: t:NEWavl -> {r:Wavl | ((rkDiff (right t) r 0) || (rkDiff (right t) r 1)) && rk t <= rk r + 2} 
                    -> {v:NEWavl | (rkDiff t v 0) || (rkDiff t v 1)} @-} 
treeR :: Tree a -> Tree a -> Tree a
treeR (Tree x 1 Nil (Tree _ 0 Nil Nil)) Nil = leaf x
treeR (Tree x n l _) r = Tree x n l r 

{-@  getMin :: t:NEWavl -> ({v:Wavl | (rkDiff t v 0) || (rkDiff t v 1) }, a) @-} 
getMin :: Tree a -> (Tree a, a)
getMin (Tree x _ Nil r) = (r, x)
getMin t@(Tree x n l r) = (delL t l', x')
  where
    (l', x')             = getMin l

{-@ demoteL :: {t:NEWavl | isNode2_2 t} -> {l:Wavl | child3 t l} -> {v:NEWavl | rkDiff t v 1 && isNode2_1 v } @-}
demoteL :: Tree a -> Tree a -> Tree a
demoteL t@(Tree a n _ r) l = Tree a (n - 1) l r

{-@ demoteR :: {t:NEWavl | isNode2_2 t} -> {r:Wavl | child3 t r} -> {v:NEWavl | rkDiff t v 1 && isNode1_2 v} @-}
demoteR :: Tree a -> Tree a -> Tree a
demoteR (Tree a n l _) r = Tree a (n - 1) l r

{-@ doubleDemoteL :: {t:NEWavl | isNode2_1 t && isNode2_2 (right t)} -> {l:Wavl | child3 t l } -> {v:NEWavl | rkDiff t v 1 && isNode2_1 v } @-}
doubleDemoteL :: Tree a -> Tree a -> Tree a
doubleDemoteL (Tree x n _ (Tree y m rl rr)) l = (Tree x (n-1) l (Tree x (m-1) rl rr))

{-@ doubleDemoteR :: {t:NEWavl | isNode1_2 t && isNode2_2 (left t) } -> {r:Wavl | child3 t r} -> {v:NEWavl | rkDiff t v 1 && isNode1_2 v} @-}
doubleDemoteR :: Tree a -> Tree a -> Tree a
doubleDemoteR (Tree x n (Tree y m ll lr) _) r = Tree x (n-1) (Tree y (m-1) ll lr) r 

{-@ rotateLeftD :: {t:NEWavl | isNode2_1 t && child1 (right t) (right (right t))} -> {l:Wavl | child3 t l}  -> {v:NEWavl | rkDiff t v 0} @-}
rotateLeftD :: Tree a -> Tree a  -> Tree a 
rotateLeftD t@(Tree z n _ (Tree y m rl@Nil rr)) l@Nil = Tree y (m+1) (leaf z) rr
rotateLeftD t@(Tree z n _ (Tree y m rl rr)) l = Tree y (m+1) (Tree z (n-1) l rl) rr 

{-@ rotateDoubleLeftD :: {t:NEWavl | isNode2_1 t && isNode1_2 (right t)} -> {l:Wavl | child3 t l}  -> {v:NEWavl | rkDiff t v 0} @-}
rotateDoubleLeftD :: Tree a -> Tree a -> Tree a
rotateDoubleLeftD (Tree z n _ (Tree y m (Tree x o rll rlr) rr)) l = Tree x n (Tree z (n-2) l rll) (Tree y (n-2) rlr rr)

{-@ rotateRightD :: {t:NEWavl | isNode1_2 t && child1 (left t) (left (left t))} -> {r:Wavl | child3 t r} -> {v:NEWavl | rkDiff t v 0} @-} 
rotateRightD :: Tree a -> Tree a -> Tree a
rotateRightD (Tree x n (Tree y m ll Nil) _) r@Nil = Tree y (m+1) ll (leaf x)
rotateRightD (Tree x n (Tree y m ll lr) _) r= Tree y (m+1) ll (Tree x (n-1) lr r) 

{-@ rotateDoubleRightD :: {t:NEWavl | isNode1_2 t && isNode2_1 (left t)} -> {r:Wavl | child3 t r}  -> {v:NEWavl | rkDiff t v 0} @-}
rotateDoubleRightD :: Tree a -> Tree a -> Tree a
rotateDoubleRightD (Tree x n (Tree y m ll (Tree z o lrl lrr)) _) r = Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr r)
-}

{-@ inline isWavlNode @-}
isWavlNode :: Tree a -> Bool
isWavlNode t = isNode1_1 t || isNode1_2 t || isNode2_1 t || isNode2_2 t

{-@ inline isNode1_1 @-}
isNode1_1 :: Tree a -> Bool
isNode1_1 t = rk (left t) + 1 == rk t && rk t == rk (right t) + 1 && not (empty t)

{-@ inline isNode1_2 @-}
isNode1_2 :: Tree a -> Bool
isNode1_2 t = rk (left t) + 1 == rk t && rk t == rk (right t) + 2 && not (empty (left t))

{-@ inline isNode2_1 @-}
isNode2_1 :: Tree a -> Bool
isNode2_1 t = rk (left t) + 2 == rk t && rk t == rk (right t) + 1 && not (empty (right t))

{-@ inline isNode2_2 @-}
isNode2_2 :: Tree a -> Bool
isNode2_2 t = rk (left t) + 2 == rk t && rk t == rk (right t) + 2 && not (empty (right t)) && not (empty (left t)) -- <- this one prohibits 2,2-leafs!!

{-@ inline child1 @-}
child1 :: Tree a -> Tree a -> Bool
child1 t s = rk t == rk s + 1

{-@ inline child2 @-}
child2 :: Tree a -> Tree a -> Bool
child2 t s = rk t == rk s + 2

{-@ inline child3 @-}
child3 :: Tree a -> Tree a -> Bool
child3 t s = rk t == rk s + 3

{- 
POtential changes for WAVL_v2 style functions: 

* promote: potT t + 1 >= tcost l + potT l + potT r + 1       | +1 if bottom case, else: 0
* rotateleft/Right: potT t + 2 >= tcost l + potT l + potT r  | +1 if bottom case, else: +2
* double rotate : -||-                                       | +1 if bottom case, else: +1 or +2, depending on children 
-}
{-@ promoteL :: {t:NEWavl | isNode1_1 t} -> {l:NEWavl | rk t == rk l} -> {v:NEWavl | rkDiff v t 1 && isNode1_2 v } @-}
promoteL :: Tree a -> Tree a -> Tree a
promoteL t@(Tree a n _ r) l = (Tree a (n+1) l r)

{-@ promoteR :: {t:NEWavl | isNode1_1 t} -> {r:NEWavl | rk t == rk r} -> {v:NEWavl | rkDiff v t 1 && isNode2_1 v } @-}
promoteR :: Tree a -> Tree a -> Tree a
promoteR t@(Tree a n l _) r = (Tree a (n+1) l r)

{-@ rotateRight :: {t:NEWavl | isNode1_2 t} 
                    -> {l:NEWavl | isNode1_2 l && rk t == rk l} -> {v:NEWavl | rkDiff t v 0 } @-}
rotateRight :: Tree a -> Tree a -> Tree a
rotateRight t@(Tree x n _ c) l@(Tree y m a b) = Tree y m a (Tree x (n-1) b c)

{-@ rotateDoubleRight ::  {t:NEWavl | isNode1_2 t} -> {l:NEWavl | isNode2_1 l && rk t == rk l} -> {v:NEWavl | rkDiff t v 0 } @-}
rotateDoubleRight :: Tree a -> Tree a  -> Tree a 
rotateDoubleRight (Tree z n _ d) l@(Tree x m a (Tree y o b c)) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 

{-@ rotateLeft :: {t:NEWavl | isNode2_1 t} -> {r:NEWavl | isNode2_1 r && rk r == rk t} -> {v:NEWavl | rkDiff t v 0 } @-}
rotateLeft :: Tree a -> Tree a -> Tree a
rotateLeft t@(Tree x n a _) r@(Tree y m b c) = Tree y m (Tree x (n-1) a b) c

{-@ rotateDoubleLeft :: {t:NEWavl | isNode2_1 t} -> {r:NEWavl | isNode1_2 r && rk r == rk t} -> {v:NEWavl | rkDiff t v 0 } @-}
rotateDoubleLeft :: Tree a -> Tree a -> Tree a
rotateDoubleLeft (Tree x n a _) r@(Tree y m (Tree z o b_1 b_2) c) = Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 

{-@ wmapPromoteL :: {t:NEWavl | isNode1_1 t} 
                    -> {l:Tick ({l':NEWavl | rk t == rk l'}) | 
                        (rk (left t) >= 0 => amortized1 (left t) l ) &&
                        (rk (left t) ==(-1) => amortized  (left t) l ) }
                    -> {v:Tick ({v':NEWavl | rkDiff v' t 1 && isNode1_2 v' })| amortized1 t v } @-}
wmapPromoteL :: Tree a -> Tick(Tree a) -> Tick (Tree a)
wmapPromoteL t@(Tree a n _ r) l = Tick (tcost l + 1) (Tree a (n+1) (tval l) r)

{-@ wmapPromoteR :: {t:NEWavl | isNode1_1 t} 
                    -> {r:Tick ({r':NEWavl | rk t == rk r'}) | 
                        (rk (right t) >= 0 => amortized1 (right t) r ) &&
                        (rk (right t) ==(-1) => amortized  (right t) r ) }
                    -> {v:Tick ({v':NEWavl | rkDiff v' t 1 && isNode2_1 v' })| amortized1 t v } @-}
wmapPromoteR :: Tree a -> Tick(Tree a) -> Tick (Tree a)
wmapPromoteR t@(Tree a n l _) r = Tick (tcost r + 1) (Tree a (n+1) l (tval r))

{-@ fmapRotateRight :: {t:NEWavl | isNode1_2 t} -> {l:Tick ({l':NEWavl | isNode1_2 l' && rk t == rk l'}) | amortized1 (left t) l}
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0 }) | amortized3 t v} @-}
fmapRotateRight :: Tree a -> Tick (Tree a) -> Tick (Tree a)
fmapRotateRight t@(Tree x n _ c) (Tick tl (Tree y m a b)) = Tick tl (Tree y m a (Tree x (n-1) b c))

{-@ fmapRotateDoubleRight :: {t:NEWavl | isNode1_2 t} -> {l:Tick ({l':NEWavl | isNode2_1 l' && rk t == rk l'}) | amortized1 (left t) l} 
                    -> {v:Tick ({v:NEWavl | rkDiff t v 0 }) | amortized3 t v} @-}
fmapRotateDoubleRight :: Tree a -> Tick (Tree a) -> Tick (Tree a)
fmapRotateDoubleRight (Tree z n _ d) (Tick tl (Tree x m a (Tree y o b c))) =  Tick tl (Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d))

{-@ fmapRotateLeft :: {t:NEWavl | isNode2_1 t} -> {r:Tick ({r':NEWavl | isNode2_1 r' && rk r' == rk t}) | amortized1 (right t) r} 
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0 }) | amortized3 t v} @-}
fmapRotateLeft :: Tree a -> Tick (Tree a) -> Tick (Tree a)
fmapRotateLeft t@(Tree x n a _) (Tick tl (Tree y m b c)) = Tick tl (Tree y m (Tree x (n-1) a b) c)

{-@ fmapRotateDoubleLeft :: {t:NEWavl | isNode2_1 t} -> {r:Tick ({r':NEWavl | isNode1_2 r' && rk r' == rk t}) | amortized1 (right t) r} 
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0 }) | amortized3 t v} @-}
fmapRotateDoubleLeft :: Tree a -> Tick (Tree a) -> Tick (Tree a)
fmapRotateDoubleLeft (Tree x n a _) (Tick (tl) (Tree y m (Tree z o b_1 b_2) c)) = Tick tl (Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c)) 

{-@ inTreeL :: t:NEWavl -> {l:Tick ({l':NEWavl | rk l' < rk t && (rkDiff l' (left t) 0 || rkDiff l' (left t) 1)}) |
                     (rkDiff (tval l) (left t) 0 => amortized3 (left t) l) &&
                     (rkDiff (tval l) (left t) 1 => amortized1 (left t) l) } 
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0}) | amortized3 t v } @-} -- amortized3 t v
inTreeL :: Tree a -> Tick (Tree a) -> Tick (Tree a)
inTreeL t@(Tree x n _ r) l = Tick (tcost l) (Tree x n (tval l) r)

{-@ inTreeR :: t:NEWavl -> {r:Tick ({r':NEWavl | rk r' < rk t && (rkDiff r' (right t) 0 || rkDiff r' (right t) 1)}) |
                     (rkDiff (tval r) (right t) 0 => amortized3 (right t) r) &&
                     (rkDiff (tval r) (right t) 1 => amortized1 (right t) r) } 
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0}) | amortized3 t v } @-}
inTreeR :: Tree a -> Tick (Tree a) -> Tick (Tree a)
inTreeR t@(Tree x n l _) r = Tick (tcost r) (Tree x n l (tval r))

{-@ inline amortized3 @-}
{-@ amortized3 :: Wavl -> Tick (Wavl) -> Bool @-}
amortized3 :: Tree a -> Tick (Tree a) -> Bool
amortized3 t v = potT t + 3 >= tcost v + pot v

{-@ inline amortized1 @-}
{-@ amortized1 :: Wavl -> Tick (Wavl) -> Bool @-}
amortized1 :: Tree a -> Tick (Tree a) -> Bool
amortized1 t v = potT t + 1 >= tcost v + pot v

{-@ inline amortized @-}
{-@ amortized :: Wavl -> Tick (Wavl) -> Bool @-}
amortized :: Tree a -> Tick (Tree a) -> Bool
amortized t v = potT t >= tcost v + pot v

{-@ reflect ?? @-}
{-@ (??) :: a -> y:b -> {v:b | v == y } @-}
(??) :: a -> b -> b
x ?? y = y

{-@ assert :: {v:Bool | v == True } -> Bool @-}
assert :: Bool -> Bool
assert _ = True

-- {-@ f :: a:Int -> k:Int -> {(a < k && k <= a + 2) => (a + 2 == k ) || (a + 1 == k)} @-}
-- f:: Int -> Int -> ()
-- f _ _ =  trivial

-- {-@ wavlStructLemma :: v:Wavl -> {empty v || isWavlNode v} @-}
-- wavlStructLemma :: Tree a -> ()
-- wavlStructLemma Nil =  trivial
-- wavlStructLemma _ =  trivial
