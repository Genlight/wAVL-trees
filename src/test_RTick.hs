{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Test_Rtick where

import Prelude hiding (pure, ap)
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

{-@ tickWrapper :: x:a -> {n:Int | n >= 0} -> l:Tree a -> b:Tree a -> r:Tick ({r':Tree a |  b == r'}) -> {t:Tick ({t':Tree a | val t' == x && rk t' == n && left t' == l && b == right t'}) | tcost t == tcost r } @-}
tickWrapper :: a -> Int -> Tree a -> Tree a -> Tick (Tree a) -> Tick (Tree a)
tickWrapper x n l _ r = (pure tree) `ap` (pure x) `ap` (pure n) `ap` (pure l) `ap` r

{-@ tree :: x:a -> {n:Int | n >= 0} -> l:Tree a -> r:Tree a -> {t:Tree a | rk t == n && left t == l && right t == r && val t == x} @-}
tree :: a -> Int -> Tree a -> Tree a -> Tree a
tree x n l r = Tree x n l r 

-- Test
main = do
    mapM_ print [a,b,c]
  where
    a = Tree 8 0 Nil Nil
    b = Tree 3 0 Nil Nil
    c = Tree 5 2 a b
    -- d = tval (tickWrapper 5 2 a b (pure b))