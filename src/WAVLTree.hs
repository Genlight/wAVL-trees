module WAVLTree
    ( insert, 
    -- delete
    ) where

import Prelude hiding (max)
-- data Leaf = Nothing 

{-@ inline max @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

-- define Orderedness
{-@ type TreeL a X = Tree {v:a | v < X }  @-}
{-@ type TreeR a X = Tree {v:a | X < v }  @-}

{-@ type OrdVal = a:Ord @-}
{-@ type LeafRank = {v:Int | v >= -1 } @-}
{-@ data Tree [rk] 
                         @-}
data Tree a = Leaf | Tree (Tree a) a Int (Tree a) deriving (Show)

{-@ type Wavl a = {v:Tree a | rankbalanced v } @-}

-- invariant section
{-@ measure notEmptyTree @-}
notEmptyTree :: Tree a -> Bool
notEmptyTree Leaf = False
notEmptyTree _ = True

-- to show functional correctnesss we need to make the connection between ranks and the nodes Height, analog to AVL trees and show that the theorem holds
--  that realHeight <= 2 lg n

{-@ measure nodeHeight @-}
nodeHeight :: Tree a -> Int
nodeHeight Leaf = -1
nodeHeight (Tree l _ _ r) = 1 + max hl hr
  where
    hl         = nodeHeight l
    hr         = nodeHeight r

-- {-@ invariant {v:Wavl a | notEmptyTree v => -1 < rk v && realHeight v <= rk v && rk v <= 2 * realHeight v } @-}

{-@ measure inv_height  :: t:Tree -> {v:Bool | notEmptyTree t ==> -1 < rk t && realHeight t <= rk t && rk t <= 2 * realHeight t } @-}
inv_height :: Tree a -> Bool
inv_height Leaf           = True
inv_height (Tree l _ _ r) = inv_height l && inv_height r


-- Rank Rule: if node is a parent with only leaf (NIL) children then we only allow nodes of rank 0, no 2,2-nodes allowed at that rank
-- otherwise we only allow a rank difference betw. 1 and 2 
{-@ measure isRankParent @-}
isRankParent :: Tree a -> Bool
isRankParent Leaf = True
isRankParent (Tree l _ rank r) = rk l < rank && rk l + 2 >= rank && rk r < rank && rk r + 2 >= rank  

{-@ measure rankbalanced @-}
rankbalanced :: Tree a -> Bool
rankbalanced Leaf = True
rankbalanced t@(Tree l _ n r) = isRankParent t && rankbalanced l && rankbalanced r 

{-@ measure inv_Rank2Height @-}
inv_Rank2Height :: Tree a -> Bool
inv_Rank2Height Leaf = True
inv_Rank2Height t@(Tree l _ n r) = nodeHeight t <= n && n <= 2 * nodeHeight t && inv_Rank2Height l && inv_Rank2Height r


-- {-@ measure height @-}
{-@ type WavlN a n = {v:Wavl | nodeHeight v == n } @-}
{-@ singleton :: a -> t:{WavlN a 0} @-}
singleton :: a -> Tree a
singleton x =  (Tree Leaf x 0 Leaf)

{-@ insert :: a => Wavl a -> Wavl a @-}
insert :: (Ord a) => a -> Tree a -> Tree a
insert x Leaf              = singleton x
insert x t@(Tree l a n r) 
    | x < a = balL (Tree (insL x l) a n r)
    | x > a = balR (Tree l a n (insert x r))
    | otherwise = t 
    where 

-- add it as a measure or inline
{-@ measure rk @-}
{-@ rk :: Wavl a -> LeafRank @-}
rk :: Tree a -> Int
rk Leaf =  -1
rk (Tree _ _ n _) = n
 
balL :: Tree a -> Tree a
balL Leaf = Leaf
balL t@(Tree ab x n c) 
    | rk ab < n = t
    | otherwise = if rk ab == rk c + 1 then Tree ab x (n+1) c -- promote
        else case ab of 
          (Tree a y m b) -> if rk b + 2 == m then Tree a y m (Tree b x (n-1) c)
            else case b of 
              (Tree b_1 z o b_2) -> Tree (Tree a y (m-1) b_1) z (o+1) (Tree b_2 x (n-1) c) 
              

balR :: Tree a -> Tree a
balR Leaf = Leaf
balR t@(Tree a x n bc) 
    | rk bc < n = t       -- stop case
    | otherwise = if rk bc == rk a + 1 then (Tree a x (n+1) bc) --promote
        else case bc of 
          (Tree b y m c) -> if rk b + 2 == m then (Tree (Tree a x (n-1) b) y m c) -- single rotation
            else case b of 
              (Tree b_1 z o b_2) -> Tree (Tree a x (n-1) b_1) z (o+1) (Tree b_2 y (m-1) c) -- double rotation
