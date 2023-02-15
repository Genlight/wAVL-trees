Good day to you all, 
I am currently working with the RTick library and having some problemsproving properties of my wrapped structures, i.e. 

I have a tree binary tree structure with a "rank" value, for which I 

which I want to show/check that the following holds: 

```haskell
-- this is LH `safe`
{-@ tickWrapperR :: x:a -> {n:Int | n >= 0} -> l:Tree a -> r:Tick (Tree a) -> {t:Tick ({t':Tree a | val t' == x && rk t' == n && left t' == l  }) | tcost t == tcost r } @-}
tickWrapperR :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
tickWrapperR x n l r = (pure tree') `ap` (pure x) `ap` (pure n) `ap` (pure l) `ap` r
```

```haskell
-- this is LH `unsafe`
{-@ tickWrapperR :: x:a -> {n:Int | n >= 0} -> l:Tree a -> r:Tick (r':Tree a) -> {t:Tick ({t':Tree a | val t' == x && rk t' == n && left t' == l && tval r == right t' }) | tcost t == tcost r } @-}
```

In my environment, I am using LH as the GHC plugin, v8.10.7, z3 v4.8.7, Ubuntu 20.04.
When running my project with stack build

I also made an example in the LH online editor: [http://goto.ucsd.edu:8090/index.html#?demo=permalink%2F1676459829_19976.hs]