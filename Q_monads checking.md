Good day to you all, 
I am currently working with the RTick library and having some problemsproving properties of my wrapped structures, i.e. 

I have a tree binary tree structure with a "rank" value, for which I want to show/check that the following holds: 

```haskell
-- this is LH `safe`
{-@ tickWrapperR :: x:a -> {n:Int | n >= 0} -> l:Tree a -> r:Tick (Tree a) -> {t:Tick ({t':Tree a | val t' == x && rk t' == n && left t' == l  }) | tcost t == tcost r } @-}
tickWrapperR :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
tickWrapperR x n l r = (pure tree') `ap` (pure x) `ap` (pure n) `ap` (pure l) `ap` r
```

```haskell
-- this is LH `unsafe` in my editor, while `safe` in the online editor
{-@ tickWrapperR :: x:a -> {n:Int | n >= 0} -> l:Tree a -> r:Tick ({r':Tree a | tval r == r'}) -> {t:Tick ({t':Tree a | val t' == x && rk t' == n && left t' == l && tval r == right t' }) | tcost t == tcost r } @-}
```
I get an "Illegal type specification/Unbound symbol error for `r` usage inside of the clause `{r':Tree a | tval r == r'}`

In my environment, I am using LH as the GHC plugin, v8.10.7, z3 v4.8.7, Ubuntu 20.04. my project is downloadable at [https://github.com/Genlight/lhTest] and should be able to build with stack. The test file is [test_RTick.hs](src/test_RTick.hs). 

LH version used: 
```bash
$ stack exec liquid -- --version
LiquidHaskell Version 0.8.10.7.1 no git information
Copyright 2013-19 Regents of the University of California. All Rights Reserved.
```

Until now, everything seemed to check out fine, I got the same errors as with the online editor. Is there a version difference between my used version of LH and the one used in the online editor?

I also made an example in the LH online editor (the safe one): [http://goto.ucsd.edu:8090/index.html#?demo=permalink%2F1676459829_19976.hs]