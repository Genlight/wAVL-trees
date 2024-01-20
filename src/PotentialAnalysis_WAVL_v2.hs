{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--bscope" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--diff" @-}

module PotentialAnalysis_WAVL_v2 where

import Prelude hiding (pure, sum)
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
{-@ rk :: t:Tree a -> {v:Int | (empty t <=> v == (-1)) && ( not (empty t) <=> v >= 0 )} @-} -- && (v >= 0 => not (empty v))
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
                    && ((rkDiff t s 1 && rk s >= 0) => (isNode1_2 t || isNode2_1 t)) } ) | amortizedStmt s t' &&
                    (empty s => amortized s t' ) } @-}
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
            | rk l'' < rk t = inTreeL t l'
            | isNode1_1 t = promoteL t l'
            | isNode1_2 t && isNode1_2 l'' = rotateRight t l'
            | isNode1_2 t && isNode2_1 l'' = rotateDoubleRight t l'
        insR 
            | rk r'' < rk t = inTreeR t r'
            | isNode1_1 t = promoteR t r'
            | isNode2_1 t && isNode2_1 r'' = rotateLeft t r'
            | isNode2_1 t && isNode1_2 r'' = rotateDoubleLeft t r'

 
{-@ delete :: (Ord a) => a -> t:Wavl -> {v:Tick ({v':Wavl | ((rkDiff t v' 0) || (rkDiff t v' 1))}) | amortDelStmt t v} @-}
delete::  (Ord a) => a -> Tree a -> Tick (Tree a)
delete _ Nil = pure Nil
delete y t@(Tree x n l r) = case compare x y of
    LT -> delL t l'
    GT -> delR t r'
    EQ -> merge
    where
        l' = delete x l
        r' = delete x r
        merge 
            | empty r = pure l
            | otherwise = let (r'', z) = getMin r in delR (Tree z n l r) r''

{-@  getMin :: t:NEWavl -> ({v:Tick {v':Wavl | (rkDiff t v' 0) || (rkDiff t v' 1) } | amortDelStmt t v}, a) @-} 
getMin :: Tree a -> (Tick (Tree a), a)
getMin (Tree x _ Nil r) = ((pure r), x)
getMin t@(Tree x n l r) = (delL t l', x')
  where
    (l', x')             = getMin l

{-@ delR :: t:NEWavl -> {r:Tick ({r':Wavl | ((rkDiff (right t) r' 0) || (rkDiff (right t) r' 1))}) | amortDelStmt (right t) r} 
                    -> {v:Tick ({v':NEWavl | ((rkDiff t v' 0) || (rkDiff t v' 1))}) | amortDelStmt t v } @-}
delR :: Tree a -> Tick (Tree a) -> Tick (Tree a)
delR t@(Tree x n Nil _) r = assert (rk (tval r) <= 0) ?? treeR t r
delR t@(Tree x n l _) r 
        | rk t <= rk r' + 2 = treeR t r
        | child2 t l = demoteR t r
        | isNode2_2 l = doubleDemoteR t r
        | (isNode1_2 l || isNode1_1 l) = rotateRightD t r
        | (isNode2_1 l) = rotateDoubleRightD t r
            where
                r' = tval r

{-@ delL :: t:NEWavl -> {l:Tick ({l':Wavl | ((rkDiff (left t) l' 0) || (rkDiff (left t) l' 1))}) | 
                    amortDelStmt (left t) l}
                    -> {v:Tick ({v':NEWavl | ((rkDiff t v' 0) || (rkDiff t v' 1))}) | amortDelStmt t v } @-}
delL :: Tree a -> Tick (Tree a) -> Tick (Tree a)
delL t@(Tree x n _ r@Nil) l = assert (rk (tval l) <= 0) ?? treeL t l 
delL t@(Tree x n _ r) l
        | rk t <= rk l' + 2 =  treeL t l
        | child2 t r  = demoteL t l
        | isNode2_2 r = doubleDemoteL t l
        | (isNode1_1 r || isNode2_1 r) = rotateLeftD t l
        | (isNode1_2 r) = rotateDoubleLeftD t l
            where 
                l' = tval l

{-@ inline amortDelStmt @-}
{-@ amortDelStmt :: Wavl -> Tick (Wavl) -> Bool @-}
amortDelStmt :: Tree a -> Tick (Tree a) -> Bool
amortDelStmt t v = ((rkDiff t (tval v) 0) || (amortized t v) ) 
                    && (rkDiff t (tval v) 1 || (amortized3 t v))

{-@ treeL :: t:NEWavl -> {l:Tick ({l':Wavl | ((rkDiff (left t) l' 0) || (rkDiff (left t) l' 1))}) | 
                    amortDelStmt (left t) l && rk t <= rk (tval l) + 2 }
                    -> {v:Tick ({v':NEWavl | (rkDiff t v' 0) || (rkDiff t v' 1)}) | amortDelStmt t v} @-} 
treeL :: Tree a -> Tick (Tree a) -> Tick (Tree a)
treeL (Tree x 1 (Tree _ 0 Nil Nil) Nil) (Tick _ Nil) = pure (leaf x) -- implicit demote step, demotes 2,2-leaf to 1,1
treeL (Tree x n _ r) l = Tick (tcost l) (Tree x n (tval l) r)

{-@ treeR :: t:NEWavl -> {r:Tick ({r':Wavl | ((rkDiff (right t) r' 0) || (rkDiff (right t) r' 1))}) | 
                    amortDelStmt (right t) r && rk t <= rk (tval r) + 2 }
                    -> {v:Tick ({v':NEWavl | (rkDiff t v' 0) || (rkDiff t v' 1)}) | amortDelStmt t v} @-} 
treeR :: Tree a -> Tick (Tree a) -> Tick (Tree a)
treeR (Tree x 1 Nil (Tree _ 0 Nil Nil)) (Tick _ Nil) = pure (leaf x) -- implicit demote step, demotes 2,2-leaf to 1,1
treeR (Tree x n l _) r = Tick (tcost r) (Tree x n l (tval r))

{-@ demoteL :: {t:NEWavl | isNode2_2 t} -> {l:Tick (Wavl) | child3 t (tval l) && amortized (left t) l} 
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 1}) | amortized t v } @-}
demoteL :: Tree a -> Tick (Tree a) -> Tick (Tree a)
demoteL t@(Tree a n _ r) l = Tick (tcost l + 1) (Tree a (n - 1) (tval l) r)

{-@ demoteR :: {t:NEWavl | isNode2_2 t} -> {r:Tick (Wavl) | child3 t (tval r) && amortized (right t) r} -> {v:Tick ({v':NEWavl | rkDiff t v' 1 }) | amortized t v } @-}
demoteR :: Tree a -> Tick (Tree a) -> Tick (Tree a)
demoteR (Tree a n l _) r = Tick (tcost r + 1) (Tree a (n - 1) l (tval r))

{-@ doubleDemoteL :: {t:NEWavl | isNode2_1 t && isNode2_2 (right t)} -> {l:Tick (Wavl) | child3 t (tval l) && amortized (left t) l} 
        -> {v:Tick ({v':NEWavl |  rkDiff t v' 1 }) |  amortized t v } @-}
doubleDemoteL :: Tree a -> Tick (Tree a) -> Tick (Tree a)
doubleDemoteL (Tree x n _ (Tree y m rl rr)) l = Tick (tcost l + 1) (Tree x (n-1) (tval l) (Tree x (m-1) rl rr))

{-@ doubleDemoteR :: {t:NEWavl | isNode1_2 t && isNode2_2 (left t) } -> {r:Tick (Wavl) | child3 t (tval r) && amortized (right t) r} 
        -> {v:Tick ({v':NEWavl | rkDiff t v' 1}) | amortized t v} @-}
doubleDemoteR :: Tree a -> Tick (Tree a) -> Tick (Tree a)
doubleDemoteR (Tree x n (Tree y m ll lr) _) r = Tick (tcost r) (Tree x (n-1) (Tree y (m-1) ll lr) (tval r))

{-@ rotateLeftD :: {t:NEWavl | isNode2_1 t && child1 (right t) (right (right t))} -> {l:Tick (Wavl) |  child3 t (tval l)  && amortized (left t) l}  -> {v:Tick ({v':NEWavl | rkDiff t v' 0}) | rkDiff t (tval v) 0 && amortized3 t v} @-} 
rotateLeftD :: Tree a -> Tick (Tree a) -> Tick (Tree a)
rotateLeftD t@(Tree z n _ (Tree y m rl@Nil rr)) l@(Tick _ Nil) = Tick (tcost l) (Tree y (m+1) (leaf z) rr)
rotateLeftD t@(Tree z n _ (Tree y m rl rr)) l = Tick (tcost l) (Tree y (m+1) (Tree z (n-1) (tval l) rl) rr )

{-@ rotateDoubleLeftD :: {t:NEWavl | isNode2_1 t && isNode1_2 (right t)} -> {l:Tick (Wavl) | child3 t (tval l) && amortized (left t) l}  -> {v:Tick ({v':NEWavl | rkDiff t v' 0}) | rkDiff t (tval v) 0 && amortized3 t v} @-}
rotateDoubleLeftD :: Tree a -> Tick (Tree a) -> Tick (Tree a)
rotateDoubleLeftD (Tree z n _ (Tree y m (Tree x o rll rlr) rr)) l = Tick (tcost l) (Tree x n (Tree z (n-2) (tval l) rll) (Tree y (n-2) rlr rr))

{-@ rotateRightD :: {t:NEWavl | isNode1_2 t && child1 (left t) (left (left t))} -> {r:Tick (Wavl) | child3 t (tval r) && amortized (right t) r} -> {v:Tick({v':NEWavl | rkDiff t v' 0}) | rkDiff t (tval v) 0 && amortized3 t v} @-} 
rotateRightD :: Tree a -> Tick (Tree a) -> Tick (Tree a)
rotateRightD (Tree x n (Tree y m ll Nil) _) r@(Tick _ Nil) = Tick (tcost r) (Tree y (m+1) ll (leaf x))
rotateRightD (Tree x n (Tree y m ll lr) _) r = Tick (tcost r) (Tree y (m+1) ll (Tree x (n-1) lr (tval r)))

{-@ rotateDoubleRightD :: {t:NEWavl | isNode1_2 t && isNode2_1 (left t)} -> {r:Tick (Wavl) | child3 t (tval r) && amortized (right t) r}  
        -> {v:Tick ({v':NEWavl | rkDiff t v' 0}) | rkDiff t (tval v) 0 && amortized3 t v} @-}
rotateDoubleRightD :: Tree a -> Tick (Tree a) -> Tick (Tree a)
rotateDoubleRightD (Tree x n (Tree y m ll (Tree z o lrl lrr)) _) r = Tick (tcost r) (Tree z (o+2) (Tree y (m-1) ll lrl) (Tree x (n-2) lrr (tval r)))

{-@ inline isWavlNode @-}
isWavlNode :: Tree a -> Bool
isWavlNode t = isNode1_1 t || isNode1_2 t || isNode2_1 t || isNode2_2 t

{-@ inline isNode1_1 @-}
isNode1_1 :: Tree a -> Bool
isNode1_1 t = rk (left t) + 1 == rk t && rk t == rk (right t) + 1 -- && not (empty t)

{-@ inline isNode1_2 @-}
isNode1_2 :: Tree a -> Bool
isNode1_2 t = rk (left t) + 1 == rk t && rk t == rk (right t) + 2 -- && not (empty (left t))

{-@ inline isNode2_1 @-}
isNode2_1 :: Tree a -> Bool
isNode2_1 t = rk (left t) + 2 == rk t && rk t == rk (right t) + 1 -- && not (empty (right t))

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
{-@ promoteL :: {t:NEWavl | isNode1_1 t} 
                    -> {l:Tick (NEWavl) | rk (tval l) == rk t && 
                        (rk (left t) >= 0 => amortized1 (left t) l ) &&
                        (rk (left t) ==(-1) => amortized  (left t) l ) }
                    -> {v:Tick ({v':NEWavl | rkDiff v' t 1 && isNode1_2 v' })| amortized1 t v } @-}
promoteL :: Tree a -> Tick(Tree a) -> Tick (Tree a)
promoteL t@(Tree a n _ r) l = Tick (tcost l + 1) (Tree a (n+1) (tval l) r)

{-@ promoteR :: {t:NEWavl | isNode1_1 t} 
                    -> {r:Tick (NEWavl) | rk t == rk (tval r) &&
                        (rk (right t) >= 0 => amortized1 (right t) r ) &&
                        (rk (right t) ==(-1) => amortized  (right t) r ) }
                    -> {v:Tick ({v':NEWavl | rkDiff v' t 1 && isNode2_1 v' })| amortized1 t v } @-}
promoteR :: Tree a -> Tick(Tree a) -> Tick (Tree a)
promoteR t@(Tree a n l _) r = Tick (tcost r + 1) (Tree a (n+1) l (tval r))

{-@ rotateRight :: {t:NEWavl | isNode1_2 t} -> {l:Tick (NEWavl) | rk (tval l) == rk t && isNode1_2 (tval l) && amortized1 (left t) l}
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0 }) | rkDiff t (tval v) 0 && amortized3 t v} @-}
rotateRight :: Tree a -> Tick (Tree a) -> Tick (Tree a)
rotateRight t@(Tree x n _ c) (Tick tl (Tree y m a b)) = Tick tl (Tree y m a (Tree x (n-1) b c))

{-@ rotateDoubleRight :: {t:NEWavl | isNode1_2 t} -> {l:Tick (NEWavl) | rk (tval l) == rk t && isNode2_1 (tval l) && amortized1 (left t) l} 
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0 }) | rkDiff t (tval v) 0 && amortized3 t v} @-}
rotateDoubleRight :: Tree a -> Tick (Tree a) -> Tick (Tree a)
rotateDoubleRight (Tree z n _ d) (Tick tl (Tree x m a (Tree y o b c))) =  Tick tl (Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d))

{-@ rotateLeft :: {t:NEWavl | isNode2_1 t} -> {r:Tick (NEWavl) | rk (tval r) == rk t && isNode2_1 (tval r) && amortized1 (right t) r} 
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0 }) | rkDiff t (tval v) 0 && amortized3 t v} @-}
rotateLeft :: Tree a -> Tick (Tree a) -> Tick (Tree a)
rotateLeft t@(Tree x n a _) (Tick tl (Tree y m b c)) = Tick tl (Tree y m (Tree x (n-1) a b) c)

{-@ rotateDoubleLeft :: {t:NEWavl | isNode2_1 t} -> {r:Tick (NEWavl) | rk (tval r) == rk t && isNode1_2 (tval r) && amortized1 (right t) r} 
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0 }) | rkDiff t (tval v) 0 && amortized3 t v} @-}
rotateDoubleLeft :: Tree a -> Tick (Tree a) -> Tick (Tree a)
rotateDoubleLeft (Tree x n a _) (Tick (tl) (Tree y m (Tree z o b_1 b_2) c)) = Tick tl (Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c)) 

{-@ inTreeL :: t:NEWavl -> {l:Tick (NEWavl) | ((rkDiff (tval l) (left t) 0 || rkDiff (tval l) (left t) 1)) && rk (tval l) < rk t && amortizedStmt (left t) l } 
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0}) | rkDiff t (tval v) 0 && amortized3 t v } @-}
inTreeL :: Tree a -> Tick (Tree a) -> Tick (Tree a)
inTreeL t@(Tree x n _ r) l = Tick (tcost l) (Tree x n (tval l) r)

{-@ inTreeR :: t:NEWavl -> {r:Tick (NEWavl) | rk (tval r) < rk t && ((rkDiff (tval r) (right t) 0 || rkDiff (tval r) (right t) 1)) && amortizedStmt (right t) r } 
                    -> {v:Tick ({v':NEWavl | rkDiff t v' 0}) | rkDiff t (tval v) 0 && amortized3 t v } @-}
inTreeR :: Tree a -> Tick (Tree a) -> Tick (Tree a)
inTreeR t@(Tree x n l _) r = Tick (tcost r) (Tree x n l (tval r))

{-@ inline amortized3 @-}
{-@ amortized3 :: Wavl -> Tick (Wavl) -> Bool @-}
amortized3 :: Tree a -> Tick (Tree a) -> Bool
amortized3 t v = potT t + 3 >= tcost v + pot v

{-@ inline amortized2 @-}
{-@ amortized2 :: Wavl -> Tick (Wavl) -> Bool @-}
amortized2 :: Tree a -> Tick (Tree a) -> Bool
amortized2 t v = potT t + 2 >= tcost v + pot v

{-@ inline amortized1 @-}
{-@ amortized1 :: Wavl -> Tick (Wavl) -> Bool @-}
amortized1 :: Tree a -> Tick (Tree a) -> Bool
amortized1 t v = potT t + 1 >= tcost v + pot v

{-@ inline amortized @-}
{-@ amortized :: Wavl -> Tick (Wavl) -> Bool @-}
amortized :: Tree a -> Tick (Tree a) -> Bool
amortized t v = potT t >= tcost v + pot v

{-@ inline amortizedStmt @-}
{-@ amortizedStmt :: Wavl -> Tick (Wavl) -> Bool @-}
amortizedStmt :: Tree a -> Tick (Tree a) -> Bool
amortizedStmt t v = ((rkDiff (tval v) t 1) || (amortized3 t v)) && (rkDiff (tval v) t 0 || amortized1 t v)

{-@ reflect ?? @-}
{-@ (??) :: a -> y:b -> {v:b | v == y } @-}
(??) :: a -> b -> b
x ?? y = y

{-@ assert :: {v:Bool | v == True } -> Bool @-}
assert :: Bool -> Bool
assert _ = True

{- proof of the connection fo height and rank of WAVL trees -}

{-| Theorem 3.1
  what we want to proof:
  - Height of a given Tree t is a logarithmic upper bound
|-}

{-@ measure ht @-}
{-@ ht :: Tree a -> Nat @-}
ht              :: Tree a -> Int
ht Nil          = 0
ht (Tree x n l r) = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

{-@ measure sum @-}
{-@ sum :: Tree a -> Nat @-}
sum :: Tree a -> Int
sum Nil = 0
sum (Tree _ _ l r) = 1 + sum l + sum r

{-@ reflect heightLemma @-}
{-@ heightLemma :: t:Wavl  -> Bool  / [rk t] @-}
heightLemma :: Tree a -> Bool
-- heightLemma Nil = True
heightLemma t = rk t + 1 <= 2 * (ht t) && ht t <= rk t + 1  

{-@ nilLemma :: { t:Wavl | rk t == (-1)} -> {heightLemma t } @-}
nilLemma :: Tree a -> Proof 
nilLemma t@Nil = trivial

{-@ hL0 :: {t:NEWavl | ht (left t) == ht (right t)} -> { ht (left t) + 1 == ht t  } @-}
hL0 :: Tree a -> Proof
hL0 t@(Tree _ _ l r) =  ht l =<= ht l + 1 === ht t *** QED

{-@ hL1 :: {t:NEWavl | ht (left t) > ht (right t)} -> {ht t == ht (left t) + 1} @-}
hL1 :: Tree a -> Proof
hL1 t@(Tree _ _ l r) = ht l =<= (ht l) + 1 === ht t *** QED

{-@ hL2 :: {t:NEWavl | ht (left t) < ht (right t)} -> {ht t == ht (right t) + 1} @-}
hL2 :: Tree a -> Proof
hL2 t@(Tree _ _ l r) = ht r =<= ht r + 1 === ht t *** QED

{-@ lowerHeightProof :: t:Wavl -> { ht t <= rk t + 1} / [rk t] @-}
lowerHeightProof :: Tree a -> ()
lowerHeightProof t@Nil = trivial ? nilLemma *** QED
lowerHeightProof t@(Tree _ 0 l@Nil r@Nil) = rk r + 1 
                                        === 1 + (-1) ? isWavlNode t
                                        === ht r ? nilLemma r 
                                        === rk l + 1 ? nilLemma l         
                                        === ht l
                                        =<= ht t  ? hL0 t
                                        === 1 
                                        =<= rk t + 1
                                        *** QED
lowerHeightProof t@(Tree _ n l r)
  | ht l > ht r   = rk t + 1  
                =>= rk l + 1  ? lowerHeightProof l
                =>= ht l  
                =<= ht l + 1 ? hL1 t
                === ht t 
                *** QED
  | ht r > ht l   = rk t + 1
                =>= rk r + 1  ? lowerHeightProof r
                =>= ht r  
                =<= ht r + 1 ? hL2 t
                === ht t 
                *** QED
  | ht l == ht r  = rk t + 1
                =>= rk l + 1  ? lowerHeightProof l
                =>= ht l  
                =<= ht l + 1 ? hL0 t
                === ht t 
                *** QED

{-@ upperHeightProof :: t:Wavl -> { rk t + 1 <= ht t * 2 } / [rk t] @-}
upperHeightProof :: Tree a -> Proof
upperHeightProof t@Nil  = trivial
upperHeightProof t@(Tree _ 0 l r) = rk r
                                === (-1)
                                =<= 0     ? nilLemma r
                                === ht r  
                                === rk l + 1 ? nilLemma l         
                                === ht l
                                =<= ht t  ? hL0 t        
                                === 1
                                === rk t + 1
                                =<= ht t * 2 
                                *** QED
upperHeightProof t@(Tree _ n l r) 
  | ht l == ht r  = rk t           
                =<= rk l + 2       ? upperHeightProof l
                =<= 2 * ht l + 2   
                === 2 * (ht l + 1) ? hL0 t
                =<= 2 * ht t
                *** QED
  | ht l > ht r   = rk t           
                =<= rk l + 2       ? upperHeightProof l
                =<= 2 * ht l + 2  
                === 2 * (ht l + 1) ? hL1 t
                =<= 2 * ht t
                *** QED
  | ht r > ht l   = rk t            
                =<= rk r + 2        ? upperHeightProof r
                =<= 2 * (ht r) + 2  
                === 2 * (ht r + 1) ? hL2 t      
                =<= 2 * ht t
                *** QED

{-@ heightProof :: t:Wavl -> {heightLemma t} @-}
heightProof :: Tree a -> Proof
heightProof t@Nil = ht t === rk t + 1 ? nilLemma
                    =<= 2 * ht t *** QED 
heightProof t = ht t ? lowerHeightProof t 
            =<= rk t + 1 ? upperHeightProof t
            =<= 2 * ht t  
            *** QED
