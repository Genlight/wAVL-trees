{-# LANGUAGE QuasiQuotes #-}

import LiquidHaskell

data Tree a = Leaf
            | Node { value :: a
                   , left  :: Tree a
                   , right :: Tree a
                   }

{-@ data Tree a = Leaf
                | Node { value :: a
                       , left  :: Tree {v:a | v >= value}
                       , right :: Tree {v:a | v >= value}
                       }
@-}

-- Example functions operating on Tree Heaps

-- -- Function to insert a value into a tree heap
-- {-@ insert :: (Ord a) => a -> Tree a -> Tree a @-}
-- insert :: (Ord a) => a -> Tree a -> Tree a
-- insert x Leaf = Node x Leaf Leaf
-- insert x (Node v l r)
--   | x <= v    = Node v (insert x r) l
--   | otherwise = Node v l (insert x r)

-- -- Function to find the minimum element in a tree heap
-- {-@ findMin :: (Ord a) => Tree a -> Maybe a @-}
-- findMin :: (Ord a) => Tree a -> Maybe a
-- findMin Leaf         = Nothing
-- findMin (Node v _ _) = Just v

-- -- Function to delete the minimum element from a tree heap
-- {-@ deleteMin :: (Ord a) => Tree a -> Tree a @-}
-- deleteMin :: (Ord a) => Tree a -> Tree a
-- deleteMin Leaf = Leaf
-- deleteMin (Node _ l r) = merge l r

-- -- Helper function to merge two tree heaps
-- {-@ merge :: (Ord a) => Tree a -> Tree a -> Tree a @-}
-- merge :: (Ord a) => Tree a -> Tree a -> Tree a
-- merge Leaf t = t
-- merge t Leaf = t
-- merge t1@(Node v1 l1 r1) t2@(Node v2 l2 r2)
--   | v1 <= v2  = Node v1 (merge r1 t2) l1
--   | otherwise = Node v2 (merge t1 r2) l2
