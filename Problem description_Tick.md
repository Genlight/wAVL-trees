# Problem description
I want to prove a theorem from the wAVL tree white paper "Rank-Balanced Trees" [2], namely Theorem 4.1, which I wrote in the file [PotentialAnalysis_WAVL.hs](src/PotentialAnalysis_WAVL.hs) at line 31.

the aim of this Potential Analysis is to show that for the number of deletions d we only need d demote steps (unterminated rebalancing steps) to rebalance a tree after the removal of a single node. 

# first try
first try/ies are mainly catched in [PotentialAnalysis.hs](src/PotentialAnalysis_WAVL.hs). 

i tried to use a similar approach to the [PopPush.hs](src/PopPush.hs) by Georg Moser, but I struggled with the "transfer" of resource usage between a child and his parent tree node in a recursive function call like insert or delete: 

```haskell
{-@ delete' :: (Ord a) => a -> s:Wavl -> Tick ({t:Wavl | (EqRk s t) || (RkDiff s t 1) }) @-}
delete' :: a -> Tree a -> Tick (Tree a)
delete' _ WAVL.Nil = pure WAVL.Nil
delete' y (WAVL.Tree x n l@WAVL.Nil r@WAVL.Nil)
  | y < x     = balLDel' x n l' r
  | x < y     = balRDel' x n l r'
  | otherwise = merge' y l r n 
    where
      l' = delete' x l
      r' = delete' x r
```

In concrete, I want to analyse how many amortized demote steps in relation to delete calls are needed. 

```haskell
{-@ balLDel' :: a -> n:Rank -> Tick ({l:Wavl | Is3ChildN n l}) -> {r:MaybeWavlNode | Is2ChildN n r} -> Tick ({t:NEWavl | (rk t == n || rk t + 1 == n) }) @-}
balLDel' :: a -> Int -> Tick (Tree a) -> Tree a -> Tick (Tree a)
balLDel' x 0 (Tick _ Nil) Nil  = pure (singleton x)
balLDel' x 1 (Tick _ Nil) Nil  = pure (singleton x)
balLDel' x n (Tick s l) r | n <= (rk l) + 2 = Tick s t -- <- Problem here
                 | n == (rk l) + 3 && (rk r) + 2 == n = demoteL' t
                 | n == (rk l) + 3 && (rk r) + 1 == n && rk (left r) + 2 == (rk r) && (rk (right r)) + 2 == rk r = doubleDemoteL' t
                 | n == (rk l) + 3 && (rk r) + 1 == n && rk (right r) + 1 == rk r = rotateLeftD' t
                 | n == (rk l) + 3 && (rk r) + 1 == n && rk (right r) + 2 == rk r && rk (left r) + 1 == rk r = rotateDoubleLeftD' t
                   where
                     t = tUnionL x n l r -- <- and here
... 

{-@ demoteL' :: s:Node3_2 -> Tick ({t:NEWavl | RkDiff s t 1 }) @-}
demoteL' :: Tree a -> Tick (Tree a)
demoteL' t = go (demoteL t)
```

This approach doesn't transfer the accrued resource costs from the child node to the parent. I thought about doing something like this at first: 

```haskell
tUnionL:: a -> int -> Tree a -> Tick (Tree a) -> Tree a -> Tick (Tick a)
tUnionL x n (Tick s l) r = Tick s (Tree x n l r)
```

But this seems to violate some more things especially your safety predicate, Def. 5.2 from the white paper "Liquidate Your Assets" [1].  


# second try, using the "LList" approach
The following approach are written down in [PotentialAnalysis_WAVL_2.hs](src/PotentialAnalysis_WAVL_2.hs)

The problem of "tUnionL" led me to believe that I needed something else. After coming across the section of "Refined Lazy Lists"  i thought i could make it work with the "LList" approach.

I tried to use the approach Niki wrote in the white paper [1], i.e. using a data type with the Tick type: 

```haskell
{-@ data Tree [rk] a = Nil | Tree { val :: a, 
                                    rd :: {v:Int | v >= 0 }, 
                                    left :: RTick.Tick (Tree a),
                                    right :: RTick.Tick (Tree a) } @-} 
data Tree a = Nil | Tree {val :: a, rd :: Int,  left :: (RTick.Tick (Tree a)), right :: (RTick.Tick (Tree a))} 
```

but then I found that my introspection into the child states rank couldn't be done without further errors, i.e. the `rk` function cannot introspect the child bc the Type signature is not the same anymore.

rank function:
```haskell
{-@ measure rk @-}
{-@ rk :: t:Tree a -> {v:Rank | (not (notEmptyTree t) || v >= 0) && (notEmptyTree t || v== (-1))} @-}
rk :: Tree a -> Int
rk Nil =  -1
rk t@(Tree _ n _ _) = n
```


```haskell
{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced Nil = True
balanced t@(Tree _ n l r) = rk r < n && n <= rk r + 2 -- <- error here 
                         && rk l < n && n <= rk l + 2
                         && ((notEmptyTree l) || (notEmptyTree r) || (n == 0)) -- disallow 2,2-leafs
                         && (balanced l)
                         && (balanced r)
```

I could further change rk to this:

```haskell
{-@ measure rk @-}
{-@ rk :: Tick (t:Tree a) -> {v:Rank | (not (notEmptyTree t) || v >= 0) && (notEmptyTree t || v== (-1))} @-}
rk :: Tick (Tree a) -> Int
rk (Tick _ (Nil)) =  -1
rk (Tick _ t@(Tree _ n _ _)) = n
```

But i think I am violating the safety property of the RTick library by pattern matching the Tick constructor like this, s. Definition 5.2, at p. 24, "Liquidate your Assets" [1]

# My conclusion

Currently, I cannot see a way to use the RTick library in connection with a Tree like structure. Mainly bc the Tree structure is hidden in the recursive call while in the examples i saw in [1] are mainly list like expressions, which can be concatenated. 

My Potential Analysis needs to reason about the structure, i.e. we don't want to count the number of recursive calls to the delete function, which i think could still be done. But we want to analyse the number of rebalancing steps, and for that we need to look deep into the `balDelL` and `balDelR` functions. 

## References
[1] Handley, M. A. T., et al. (2019). "Liquidate your assets: reasoning about resource usage in liquid Haskell." Proceedings of the ACM on Programming Languages 4(POPL): 1-27.

[2] Haeupler, B., et al. (2015). "Rank-Balanced Trees." ACM Transactions on Algorithms 11(4): 1-26.
	
