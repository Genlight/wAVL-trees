module WAVLTree
    ( insert, 
    -- delete
    ) where

{-@ LIQUID "--structural" @-}


import Prelude hiding (max)
-- data Leaf = Nothing 

{-@ inline max @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

-- define Orderedness
{-@ type WavlL a X = Wavl {v:a | v < X }  @-}
{-@ type WavlR a X = Wavl {v:a | X < v }  @-}


{-@ type OrdVal = a:Ord @-}
{-@ type LeafRank = {v:Int | v >= -1 } @-}
{-@ data Wavl a = Leaf | Node { 
                        l    :: WavlL a key
                      , key  :: a:OrdVal 
                      , rank :: {v:LeafRank | isRankParent l r v }
                      , r    :: WavlR a key
                      }   @-}
data Wavl a = Leaf | Node (Wavl a) a Int (Wavl a) deriving (Show)

-- invariant section
{-@ measure notEmptyTree @-}
notEmptyTree :: Wavl a -> Bool
notEmptyTree Leaf = False
notEmptyTree _ = True

{-@ measure inv_RankDif @-}
inv_RankDif :: Wavl a -> Bool
inv_RankDif Leaf = True
inv_RankDif (Node l _ rank r) = rk l < rank && rk r < rank     

-- to show functional correctnesss we need to make the connection between ranks and the nodes Height, analog to AVL trees and show that the theorem holds
--  that realHeight <= 2 lg n

{-@ measure nodeHeight @-}
-- {-@ nodeHeight ::  Wavl a -> Int @-}
nodeHeight :: Wavl a -> Int
nodeHeight Leaf = -1
nodeHeight (Node l _ _ r) = 1 + max hl hr
  where
    hl         = nodeHeight l
    hr         = nodeHeight r

-- {-@ invariant {v:Wavl a | notEmptyTree v => -1 < rk v && realHeight v <= rk v && rk v <= 2 * realHeight v } @-}

{-@ measure inv_proof  :: t:Wavl a -> {v:_ | notEmptyTree t ==> -1 < rk t && realHeight t <= rk t && rk t <= 2 * realHeight t } @-}
inv_proof :: Wavl a -> Bool
inv_proof Leaf           = True
inv_proof (Node l _ _ r) = inv_proof l && inv_proof r


-- Rank Rule: if node is a parent with only leaf (NIL) children then we only allow nodes of rank 0, no 2,2-nodes allowed at that rank
-- otherwise we only allow a rank difference betw. 1 and 2 
{-@ measure isRankParent @-}
isRankParent :: Wavl a -> Wavl a -> Int -> Bool
isRankParent Leaf Leaf rank = rank == 0
isRankParent l r rank = rk l < rank && rk l + 2 >= rank && rk r < rank && rk r + 2 >= rank  

{-@ measure isRankReal @-}
isRankReal :: Wavl a -> Bool
isRankReal Leaf = True
isRankReal t@(Node l _ n r) = nodeHeight t <= n && n <= 2 * nodeHeight t && isRankReal l && isRankReal r


-- {-@ measure height @-}
-- {-@ @-}
{-@ type WavlN a n = {v:Wavl | nodeHeight v == n } @-}
{-@ singleton :: a -> WavlN a 1 @-}
singleton :: a -> Wavl a
singleton x =  Node Leaf x 0 Leaf

{-@ insert :: (Ord a) => Wavl a -> Wavl a @-}
insert :: (Ord a) => a -> Wavl a -> Wavl a
insert x Leaf              = singleton x
insert x t@(Node l a n r) 
    | x < a = balL (Node (insert x l) a n r)
    | x > a = balR (Node l a n (insert x r))
    | otherwise = t 

-- add it as a measure or inline
{-@ measure rk @-}
{-@ rk :: Wavl a -> LeafRank @-}
rk :: Wavl a -> Int
rk Leaf =  -1
rk (Node l a n r) = n
 
balL :: Wavl a -> Wavl a
balL Leaf = Leaf
balL t@(Node ab x n c) 
    | rk ab < n = t
    | otherwise = if rk ab == rk c + 1 then Node ab x (n+1) c -- promote
        else case ab of 
          (Node a y m b) -> if rk b + 2 == m then Node a y m (Node b x (n-1) c)
            else case b of 
              (Node b_1 z o b_2) -> Node (Node a y (m-1) b_1) z (o+1) (Node b_2 x (n-1) c) 
              

balR :: Wavl a -> Wavl a
balR Leaf = Leaf
balR t@(Node a x n bc) 
    | rk bc < n = t       -- stop case
    | otherwise = if rk bc == rk a + 1 then (Node a x (n+1) bc) --promote
        else case bc of 
          (Node b y m c) -> if rk b + 2 == m then (Node (Node a x (n-1) b) y m c) -- single rotation
            else case b of 
              (Node b_1 z o b_2) -> Node (Node a x (n-1) b_1) z (o+1) (Node b_2 y (m-1) c) -- double rotation