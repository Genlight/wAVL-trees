{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--bscope" @-}
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--ple" @-}

module AssertFalse where

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

-- {-@ type Wavl = {v:Tree a | structLemma v } @-}
-- {-@ type NEWavl = {v:Tree a | not (empty v) } @-}

{-@ measure rk @-}
{-@ rk :: t:Tree a -> {v:Int | (empty t => v == (-1)) && ( not (empty t) => v >= 0)} @-}
rk :: Tree a -> Int
rk Nil =  -1
rk t@(Tree _ n _ _) = n

{-@ measure empty @-}
empty :: Tree a -> Bool
empty Nil = True
empty _ = False


{-@ inline isWavlNode @-}
isWavlNode :: Tree a -> Bool
isWavlNode t = isNode1_1 t || isNode1_2 t || isNode2_1 t || isNode2_2 t

{-@ inline isNode1_1 @-}
isNode1_1 :: Tree a -> Bool
isNode1_1 t = rk (left t) + 1 == rk t && rk t == rk (right t) + 1 && not (empty t)

{-@ inline isNode1_2 @-}
isNode1_2 :: Tree a -> Bool
isNode1_2 t = rk (left t) + 1 == rk t && rk t == rk (right t) + 2

{-@ inline isNode2_1 @-}
isNode2_1 :: Tree a -> Bool
isNode2_1 t = rk (left t) + 2 == rk t && rk t == rk (right t) + 1

{-@ inline isNode2_2 @-}
isNode2_2 :: Tree a -> Bool
isNode2_2 t = rk (left t) + 2 == rk t && rk t == rk (right t) + 2


{-@ measure structLemma @-}
structLemma :: Tree a -> Bool
structLemma Nil = True
structLemma t@(Tree _ n l r) = isWavlNode t && structLemma l && structLemma r 

{-@ wavlStructLemma :: v:Tree a -> {empty v || isWavlNode v} @-}
wavlStructLemma :: Tree a -> ()
wavlStructLemma Nil =  trivial
wavlStructLemma _ =  trivial

{-@ reflect ?? @-}
{-@ (??) :: a -> y:b -> {v:b | v == y } @-}
(??) :: a -> b -> b
x ?? y = y

{-@ assert :: {v:Bool | v == True } -> Bool @-}
assert :: Bool -> Bool
assert _ = True

test :: Tree a -> Bool
test t 
    | isWavlNode t && not (empty t) = True
    | otherwise = assert (wavlStructLemma t) ?? assert (False) ?? True