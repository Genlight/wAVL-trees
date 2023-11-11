```haskell


-- idWavlT :: Int -> Int -> a -> Int -> Tree a -> Tree a -> Tree a
-- idWavlT _ _ x n l r = idWavl x n l r

-- {-@ idWavlT ::  x:a -> n:NodeRank -> l':Tick({l:Wavl | is2ChildN n l})
--           -> {r:Wavl | rk r < n && n <= rk r + 2 } 
--           -> {prev:Wavl | (potT (tval l')) + tcost l' <= (potT prev) + 2 }
--           -> {t:NEWavl | potT t + tcost l' <= potT (Tree x n prev r) + 2 } @-} 
-- idWavlT :: a -> Int -> Tick (Tree a) -> Tree a -> Tree a ->  Tree a
-- idWavlT x n l r _ = idWavl x n (tval l) r

-- {-@ idWavlTR ::  x:a -> n:NodeRank -> {l:Wavl | is2ChildN n l}
--           -> r':Tick ({r:Wavl | rk r < n && n <= rk r + 2 })
--           -> {prev:Wavl | (potT (tval r')) + tcost r' <= (potT prev) + 2 }
--           -> {t:NEWavl | potT t + tcost r' <= potT (Tree x n l prev) + 2 } @-} 
-- idWavlTR :: a -> Int -> Tick (Tree a) -> Tree a -> Tree a ->  Tree a
-- idWavlTR x n l r _ = idWavl x n l (tval r)

{-
  idWavl :: check for tree 'sanity' of tuples n l r
  s. description in docs/idWavl.md
-} 
{-@ reflect idWavl @-}
{-@ idWavl :: x:a -> n:NodeRank -> {l:Wavl | is2ChildN n l} 
          -> {r:Wavl |  is2ChildN n r } 
          -> {t:NEWavl | (not (not notEmptyTree l && not notEmptyTree r) || (rk t == rk l + 1 && rk t == rk r + 1 && rk t == 0)) 
                      && ((not notEmptyTree l && not notEmptyTree r)     || (rk t == n && left t==l && right t == r)) 
                      
                      } @-}
idWavl :: a -> Int -> Tree a -> Tree a -> Tree a
idWavl x n l r
    | notEmptyTree r = idWavlR x n l r
    | notEmptyTree l = idWavlL x n l r
    | otherwise = singleton x -- not . notEmptyTree l && not . notEmptyTree r


{-@ reflect idWavlL @-}
{-@ idWavlL :: x:a -> n:NodeRank -> {l:NEWavl | is2ChildN n l} -> {r:Wavl | is2ChildN n r } 
          -> {t:NEWavl | val t == x && rk t == n && left t==l && right t == r } @-}
idWavlL :: a -> Int -> Tree a -> Tree a -> Tree a
idWavlL x n l r = Tree x n l r

{-@ reflect idWavlR @-}
{-@ idWavlR :: x:a -> n:NodeRank -> {l:Wavl | is2ChildN n l} 
          -> {r:NEWavl | rk r < n && n <= rk r + 2 } -> {t:NEWavl | rk t == n && left t==l && right t == r } @-}
idWavlR :: a -> Int -> Tree a -> Tree a -> Tree a
idWavlR x n l r = Tree x n l r

-- {-@ promoteTL :: a -> n:NodeRank -> l':Tick ({l:NEWavl | n == rk l}) 
--           -> {r:Wavl | rk (tval l') == rk r + 1 } -> {t':Tick (t:Node1_2) | tcost t' >= 0 } @-}
-- promoteTL :: a -> Int -> Tick(Tree a) -> Tree a -> Tick (Tree a)
-- promoteTL x n l r = RTick.step (tcost l + 1) . promoteL t
--   where
--     l' = tval l
--     t = RTick.step (tcost l) (pure (idAlmostWavlL x n l' r))

{-@ idAlmostWavlL :: x:a -> n:NodeRank -> {l:NEWavl | rk l <= n && n <= rk l + 2} -> {r:Wavl | rk r < n && n <= rk r + 2 } 
          -> {t:AlmostWavl | val t == x && rk t == n && left t==l && right t == r } @-}
idAlmostWavlL :: a -> Int -> Tree a -> Tree a -> Tree a
idAlmostWavlL x n l r = Tree x n l r

{-@ idAlmostWavlR :: x:a -> n:NodeRank -> {l:Wavl | is2ChildN n l } -> {r:NEWavl | rk r <= n && n <= rk r + 2} 
          -> {t:AlmostWavl | val t == x && rk t == n && left t==l && right t == r } @-}
idAlmostWavlR :: a -> Int -> Tree a -> Tree a -> Tree a
idAlmostWavlR x n l r = Tree x n l r

-- {-@ Node_0Child :: x:a -> n:NodeRank -> {l:Wavl | rk l <= n && n <= rk l + 2 } -> {r:Wavl | rk r <= n && n <= rk r + 2} 
--           -> {t:AlmostWavl | val t == x && rk t == n && left t==l && right t == r && (is0ChildN n l || is0ChildN n r)} @-}
-- Node_0Child :: a -> Int -> Tree a -> Tree a -> Tree a
-- Node_0Child x n l r = 

-- {-@ inline check1 @-}
-- {-@ check1 :: Tick (Wavl) -> Wavl -> Bool @-}
-- check1 :: Tick (Tree a) -> Tree a -> Bool
-- check1 t s 
--   | rk (tval t) == rk s = potT2 (tval t) + tcost t <= potT2 s + 2
--   | rk (tval t) == rk s + 1 = potT2 (tval t) + tcost t <= potT2 s

{-- 
  on top of the refinement declarations of insert, we know in insl that the following holds:
  * right s == right (tval t)
  * left (s) == (EqRk s (left (tval t))) || RkDiff (left (tval t)) (left s) 1  
--}
{-@ insl :: x:a -> s:NEWavl -> t':EqT s / [rk s] @-}
insl :: (Ord a) => a -> Tree a -> Tick (Tree a)
insl x t@(Tree v n l r) 
  | rk l'' < n                             = assert (rk (tval l') < n) ?? treeLW1 v n l' r -- assert (amortized1 l' l) ?? (treeL v n l' r) -- is not accepted
  | is0ChildN n l'' && rk l'' == rk r + 1  = undefined -- assert (amortized l' l) ?? (RTick.wmap promoteL (treeL v n l' r) )
  | is0ChildN n l''                        = undefined -- assert (amortized l' l) ?? (RTick.fmap balL (treeL v n l' r))
  | otherwise = pure (t)
    where
      l' = insert x l
      l'' = tval l'
      
  ```