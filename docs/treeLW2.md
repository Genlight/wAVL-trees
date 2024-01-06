this is accepted (commit: )
```haskell
-- version 2 of treeLW2, works without the amortized3 stmt
{-@ treeLW2 :: s:NEWavl -> {l:EqTL s | amortized3 l (pure (left s)) && is2Child s (tval l)} 
          -> {v:Tick ({v':NEWavl | right v' == right s && Is2Child v' (tval l) && rk s == rk v' && IsWavlNode v' }) 
          | tcost v == tcost l
            && tval v == Tree (val s) (rk s) (tval l) (right s)
            && potT (left s) + 3 >= pot1 l + tcost l 
            && potT (right s) == potT (right (tval v))
            && pot1 v >= pot1 l + potT (right s)
            && is2Child (tval v) (tval l)
            } @-}
treeLW2 :: Tree a -> Tick(Tree a) -> Tick(Tree a)
treeLW2 t@(Tree x n _ r) l = Tick (tcost l) (Tree x n (tval l) r)
```
