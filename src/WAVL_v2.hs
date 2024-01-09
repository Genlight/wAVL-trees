{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--bscope" @-}
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--ple" @-}

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

{-@ type Wavl = {v:Tree a | structLemma v } @-}
{-@ type NEWavl = {v:Tree a | not (empty v) } @-}
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

-- {-@ insert :: (Ord a) => a -> s:Wavl -> {t:NEWavl | ((rkDiff t s 1) || (rkDiff t s 0)) } @-}
{-@ insert :: (Ord a) => a -> s:Tree a -> {t:NEWavl | ((rkDiff t s 1) || (rkDiff t s 0)) 
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
            | otherwise = undefined

--  && ((rkDiff s t 1 && rk s > 1) => (isNode1_2 t || isNode2_1 t)) 
{-@ delete :: (Ord a) => a -> s:Tree a -> {t:Tree a | ((rkDiff s t 0) || (rkDiff s t 1))  } @-}
delete::  (Ord a) => a -> Tree a -> Tree a
delete _ Nil = Nil
delete y t@(Tree x n l r) = case compare x y of
    LT -> balLDel
    GT -> undefined -- balRDel x n l r'
    EQ -> undefined -- merge y l r n 
    where
        l' = delete x l
        -- r' = delete x r
        balLDel 
            | n <= (rk l') + 2 = Tree x n l' r
            | n == (rk l') + 3 && (rk r) + 2 == n                            = demoteL t l' -- assert (n == rk l + 2 => n >= 2) ?? assert (not (empty r)) ??
            | n == (rk l') + 3 && (rk r) + 1 == n && isNode2_2 r             = doubleDemoteL t l'
            | n == (rk l') + 3 && (rk r) + 1 == n && rk (left r) + 1 == rk r = undefined -- rotateLeftD t
            | n == (rk l') + 3 && (rk r) + 1 == n && isNode2_1 r             = undefined -- rotateDoubleLeftD t
            | otherwise = 
                -- assert (n == (rk l') + 3 && (rk r) + 1 == n) ?? 
                -- assert (not (empty r)) ??
                -- assert (not (isNode1_1 r)) ??
                -- assert (not (isNode1_2 r)) ??
                -- assert (not (isNode2_1 r)) ??
                assert (wavlStructLemma r ?? not (isWavlNode r)) ??
                -- assert (not (isNode2_2 r)) ?? 
                assert (False) ?? undefined


balLDel = undefined
balRDel = undefined

{-@ demoteL :: {t:NEWavl | isNode2_2 t} -> {l:Tree a | rk l + 3 == rk t} -> {v:NEWavl | rk v + 1 == rk t && isNode2_1 v } @-}
demoteL :: Tree a -> Tree a -> Tree a
demoteL t@(Tree a n _ r) l = Tree a (n - 1) l r


-- {-@ doubleDemoteL :: {s:Node3_1 | IsNode2_2 (right s) } -> {t:NEWavl | RkDiff s t 1 && potT2 s == potT2 t + 1 } @-}
{-@ doubleDemoteL :: {t:NEWavl | isNode2_1 t && isNode2_2 (right t)} -> {l:Tree a | rk l  + 3 == rk t } -> {v:NEWavl | rkDiff t v 1 && isNode2_1 v } @-}
doubleDemoteL :: Tree a -> Tree a -> Tree a
doubleDemoteL (Tree x n _ (Tree y m rl rr)) l = (Tree x (n-1) l (Tree x (m-1) rl rr))

-- {-@ merge :: x:a -> l:Tree a -> r:Tree a 
--                     -> {v:Nat | v > rk l && v < rk r && v <= rk l + 2 && v <= rk r + 2 && (not (empty (l) || not (empty r) || v == 0)) } 
--                     -> {t:Tree a | (v == rk t) || (v == rk t + 1) } @-}
-- merge :: a -> Tree a -> Tree a -> Int ->  Tree a
-- merge _ Nil Nil _ = Nil
-- merge _ Nil r _  = r
-- merge _ l Nil _  = l
-- merge x l r n    = (balRDel y n l r')
--   where
--    (r', y)     = undefined -- getMin r



{-@ type EqW s = {t:NEWavl | (rkDiff t s 0 || rkDiff t s 1) 
                    && (not (isNode2_2 t) || (rkDiff t s 0)) 
                    && ((not (isNode1_1 t && rk t > 0)) || rkDiff t s 0) 
                    && isWavlNode t } @-}

{-@ inline isWavlNode @-}
isWavlNode :: Tree a -> Bool
isWavlNode t = isNode1_1 t || isNode1_2 t || isNode2_1 t || isNode2_2 t

{-@ inline isNode1_1 @-}
isNode1_1 :: Tree a -> Bool
isNode1_1 t = rk (left t) + 1 == rk t && rk t == rk (right t) + 1 && not (empty t)

{-@ inline isNode1_2 @-}
isNode1_2 :: Tree a -> Bool
isNode1_2 t = rk (left t) + 1 == rk t && rk t == rk (right t) + 2 -- && not (empty (left t))

{-@ inline isNode2_1 @-}
isNode2_1 :: Tree a -> Bool
isNode2_1 t = rk (left t) + 2 == rk t && rk t == rk (right t) + 1 -- && not (empty (right t))

{-@ inline isNode2_2 @-}
isNode2_2 :: Tree a -> Bool
isNode2_2 t = rk (left t) + 2 == rk t && rk t == rk (right t) + 2 -- && not (empty (right t)) && not (empty (left t))

{-@ promoteL :: {t:NEWavl | isNode1_1 t} -> {l:NEWavl | rk t == rk l} -> {v:NEWavl | rk t + 1 == rk v && left v == l && right t == right v} @-}
promoteL :: Tree a -> Tree a -> Tree a
promoteL t@(Tree a n _ r) l = (Tree a (n+1) l r)

{-@ promoteR :: {t:NEWavl | isNode1_1 t} -> {r:NEWavl | rk t == rk r} -> {v:NEWavl | rk t + 1 == rk v && right v == r && left t == left v} @-}
promoteR :: Tree a -> Tree a -> Tree a
promoteR t@(Tree a n l _) r = (Tree a (n+1) l r)

-- {-@ rotateRight :: {v:Node0_2 | IsNode1_2 (left v) } -> Tree a -> {t:NEWavl | EqRk v t } @-}
{-@ rotateRight :: {t:NEWavl | isNode1_2 t} 
                    -> {l:NEWavl | isNode1_2 l && rk t == rk l} -> {v:NEWavl | rkDiff t v 0 } @-}
rotateRight :: Tree a -> Tree a -> Tree a
rotateRight t@(Tree x n _ c) l@(Tree y m a b) = Tree y m a (Tree x (n-1) b c)

{-@ rotateDoubleRight ::  {t:NEWavl | isNode1_2 t} -> {l:NEWavl | isNode2_1 l && rk t == rk l} -> {v:NEWavl | rkDiff t v 0 } @-}
rotateDoubleRight :: Tree a -> Tree a  -> Tree a 
rotateDoubleRight (Tree z n _ d) l@(Tree x m a (Tree y o b c)) =  Tree y (o+1) (Tree x (m-1) a b) (Tree z (n-1) c d) 


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

{-@ wavlStructLemma :: v:Tree a -> {empty v || isWavlNode v} @-}
wavlStructLemma :: Tree a -> ()
wavlStructLemma Nil =  trivial
wavlStructLemma _ =  trivial
