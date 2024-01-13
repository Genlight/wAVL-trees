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

After some rewriting and proving, i found that the following holds: 
```haskell
-- version 2 of treeLW2, works without the amortized3 stmt
{-@ treeLW2 :: s:NEWavl -> {l:EqTL s | amortized3 l (pure (left s)) && is2Child s (tval l)} 
          -> {v:EqT s | tcost v == tcost l && Is2Child (tval v) (tval l)
            && tval v == Tree (val s) (rk s) (tval l) (right s)
            && potT (left s) + 3 >= pot1 l + tcost l 
            && potT (right s) == potT (right (tval v))
            && pot1 v >= pot1 l + potT (right s)
            && pot1 v <= pot1 l + potT (right s) + 2
            && potT s >= potT (left s) + potT (right s)
            && potT s <= potT (left s) + potT (right s) + 2
            && potT (left s) >= pot1 l + tcost l - 3
            && potT s >= pot1 l + tcost l - 3 + potT (right s)
            && potT s + 3 - tcost l >= pot1 l + potT (right s)
            && potT s + 5 - tcost l >= pot1 l + potT (right s) + 2
            && potT s + 5 - tcost l >= pot1 v
            && potT s + 5 >= pot1 v + tcost l
            && potT s + 5 >= pot1 v + tcost v
            } @-}
treeLW2 :: Tree a -> Tick(Tree a) -> Tick(Tree a)
treeLW2 t@(Tree x n _ r) l = Tick (tcost l) (Tree x n (tval l) r)
```

Problem: here we proved the statement `potT s + 5 >= pot1 v + tcost v` which basically doesn't give us anything, i.e. we need the `+3` instead of `+5`.
Problem lies here in the case differentiation: 

We haven't differentiated between the possibilities of l being one higher in rk then `left s`, i.e. a promote case happened in l the previous process step. 
The other case is, when l is rank equal to `left s`, then amortized3 must hold bc that is true.

in the case of `rkDiff l (left s) 1` we know that there are only two sub-cases which are valid. For both following cases we know that no prior rotation happened and only a potential increase of up to 1 happened prior due to the node insertion. 

* case 2,1-node `->` 1,1-node: +1 pot difference, result: +2
* case 2,2-node `->` 1,2-node: -2 pot difference, result: -1

Thus we can conclude that these cases are altogether amortized3