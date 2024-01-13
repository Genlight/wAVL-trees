{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--bscope" @-}
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--diff" @-}

module WAVL_v2 where

import Language.Haskell.Liquid.ProofCombinators 
-- import Language.Haskell.Liquid.RTick as RTick

-- Basic functions
-- {-@ data Tree [rd] a = Nil | Tree { val :: a, 
{-@ data Tree [rk] a = Nil | Tree { val :: a, 
                                    rd :: {v:Int | v >= 0}, 
                                    left :: ChildT a rd,
                                    right :: ChildT a rd } @-} 
data Tree a = Nil | Tree { val :: a, rd :: Int, left :: (Tree a), right :: (Tree a)} deriving Show

{-@ type ChildT a K = {v:Tree a | rk v < K && K <= rk v + 2 } @-}
-- && ((notEmptyTree l) || (notEmptyTree r) || (n == 0)) -- disallow 2,2-leafs

{-@ type Wavl = {v:Tree a | structLemma v } @-} -- structLemma v
{-@ type NEWavl = {v:Wavl | not (empty v) } @-}
-- {-@ type NEWavl = {v:Wavl | not (empty v) } @-}

{-@ measure structLemma @-}
structLemma :: Tree a -> Bool
structLemma Nil = True
structLemma t@(Tree _ n l r) = isWavlNode t && structLemma l && structLemma r 

{-@ measure rk @-}
{-@ rk :: t:Tree a -> {v:Int | (empty t => v == (-1)) && ( not (empty t) => v >= 0)} @-}
rk :: Tree a -> Int
rk Nil =  -1
rk t@(Tree _ n _ _) = n

{-@ leaf :: a -> {v:NEWavl | rk v == 0 && isNode1_1 v } @-}  --  && not (isNode2_2 v)
leaf a = Tree a 0 Nil Nil

{-@ measure empty @-}
empty :: Tree a -> Bool
empty Nil = True
empty _ = False

{-@ inline rkDiff @-}
rkDiff :: Tree a -> Tree a -> Int -> Bool
rkDiff t s n = rk t - rk s  == n

{-@ insert :: (Ord a) => a -> s:Wavl -> {t:NEWavl | ((rkDiff t s 1) || (rkDiff t s 0)) 
                    && ((rkDiff t s 1 && rk s >= 0) => (isNode1_2 t || isNode2_1 t))
                     } @-}
insert :: (Ord a) => a -> Tree a -> Tree a
insert x Nil = leaf x
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> insR
    EQ -> t
    where
        l' = insert x l
        r' = insert x r
        insL 
            | rk l' < rk t = Tree x n l' r 
            | isNode1_1 t = promoteL t l'
            | isNode1_2 t && isNode1_2 l' = rotateRight t l'
            | isNode1_2 t && isNode2_1 l' = rotateDoubleRight t l'
        insR 
            | rk r' < rk t = Tree x n l r'
            | isNode1_1 t = promoteR t r'
            | isNode2_1 t && isNode2_1 r' = rotateLeft t r'
            | isNode2_1 t && isNode1_2 r' = rotateDoubleLeft t r'

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
        (r', x)     = undefined -- getMin r

{-@ delR :: t:NEWavl -> {r:Wavl | ((rkDiff (right t) r 0) || (rkDiff (right t) r 1))} -> {v:NEWavl | ((rkDiff t v 0) || (rkDiff t v 1))} @-}
delR t@(Tree _ n l _) r 
        | rk t <= rk r + 2 = undefined -- Tree x n l r' -- ->  structlemma does not arise from it
        | child3 t r && child2 t l = demoteR t r
        | child3 t r = balRDel t r

{-@ delL :: t:NEWavl -> {l:Wavl | ((rkDiff (left t) l 0) || (rkDiff (left t) l 1))} -> {v:NEWavl | ((rkDiff t v 0) || (rkDiff t v 1))} @-}
delL t@(Tree _ n _ r) l 
        | n <= rk l + 2 = undefined -- Tree x n l' r
        | child3 t l && child2 t r = demoteL t l
        | child3 t l = balLDel t l

getMin t = undefined

{-@ balLDel :: {t:NEWavl | child2 t (left t) && child1 t (right t) } -> {l:Wavl | child3 t l } -> {v:NEWavl | ((rkDiff t v 0) || (rkDiff t v 1)) } @-}
balLDel :: Tree a -> Tree a -> Tree a
balLDel t@(Tree x n _ r@(Tree _ m rl rr)) l 
            | child2 r rr && child2 r rl = doubleDemoteL t l
            | child1 r rr = rotateLeftD t l
            | child1 r rl = rotateDoubleLeftD t l

{-@ balRDel :: {t:NEWavl | child2 t (right t) && child1 t (left t) } -> {r:Wavl | child3 t r } -> {v:NEWavl | ((rkDiff t v 0) || (rkDiff t v 1)) } @-}
balRDel :: Tree a -> Tree a -> Tree a
balRDel t@(Tree x n l@(Tree _ m ll lr) _) r 
            |  child2 l lr && child2 l ll = doubleDemoteR t r
            |  child1 l ll = rotateRightD t r
            |  child1 l lr = rotateDoubleRightD t r

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
isNode2_2 t = rk (left t) + 2 == rk t && rk t == rk (right t) + 2 && not (empty (right t)) && not (empty (left t))

{-@ inline child1 @-}
child1 :: Tree a -> Tree a -> Bool
child1 t s = rk t == rk s + 1

{-@ inline child2 @-}
child2 :: Tree a -> Tree a -> Bool
child2 t s = rk t == rk s + 2

{-@ inline child3 @-}
child3 :: Tree a -> Tree a -> Bool
child3 t s = rk t == rk s + 3

{-@ promoteL :: {t:NEWavl | isNode1_1 t} -> {l:NEWavl | rk t == rk l} -> {v:NEWavl | rk t + 1 == rk v && left v == l && right t == right v} @-}
promoteL :: Tree a -> Tree a -> Tree a
promoteL t@(Tree a n _ r) l = (Tree a (n+1) l r)

{-@ promoteR :: {t:NEWavl | isNode1_1 t} -> {r:NEWavl | rk t == rk r} -> {v:NEWavl | rk t + 1 == rk v && right v == r && left t == left v} @-}
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

{-@ reflect ?? @-}
{-@ (??) :: a -> y:b -> {v:b | v == y } @-}
(??) :: a -> b -> b
x ?? y = y

{-@ assert :: {v:Bool | v == True } -> Bool @-}
assert :: Bool -> Bool
assert _ = True

{-@ f :: a:Int -> k:Int -> {(a < k && k <= a + 2) => (a + 2 == k ) || (a + 1 == k)} @-}
f:: Int -> Int -> ()
f _ _ =  trivial

{-@ wavlStructLemma :: v:Wavl -> {empty v || isWavlNode v} @-}
wavlStructLemma :: Tree a -> ()
wavlStructLemma Nil =  trivial
wavlStructLemma _ =  trivial
