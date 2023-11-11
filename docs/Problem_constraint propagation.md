in commit 1b9232db7e327e3d4b47d0f9a0331b469d849321 we had the problem, 

that the condition `rk (tval r')` in the function `insert` was not propagated to the expression and we got the LH unsafe message: 
```bash
Liquid Type Mismatch
.
The inferred type
  VV : {v : (PotentialAnalysis_WAVL.Tree a) | balanced v  ... }
...

is not a subtype of the required type
  VV : {VV : (PotentialAnalysis_WAVL.Tree a) | n > rk VV}
```

which seems ridiculous bc the pattern for insR was like this: 
```Haskell
insert :: (Ord a) => a -> Tree a -> Tick (Tree a)
insert x t@(Tree v n l r) = ...

r' = insert x r
...
 insR | is2ChildN n (tval r') = treeRW1 v n l r'
```

Here, we have again the problem that LH and specifically the RTick framework is not able to propagate the constraints from the wrapped value `r'` to the function `treeRW1`, which has a refinement for the `r` like this: 

```Haskell
{-@ r:Tick ({r':ChildB n | notEmptyTree r'}) @-}
...

-- and with
{-@ type ChildB K = {v:Wavl | Is2ChildN K v } @-}
```

## things i tried

### let instead of where
I thought that maybe exchanging `r'` in the `where` clause for a similar `let` construct would give me more control over `r'` constraints but similar issues arise there. 

### connecting tval l with itself
I tried to set `tval l == l'` where `l'` was `tval l` but this did no good and returned the error: 
```bash
is not a subtype of the required type
  VV : {VV : (PotentialAnalysis_WAVL.Tree a) | rk (tval (insert x l)) == rk VV }

```

# conclusion: what worked

In the end, the trick was to instead adding the refinement on the inner Tree level we needed to add it to the Tick wrapper. 
Instead of
```Haskell
 
```

we needed this: 
```Haskell
treeLW1 :: x:a -> n:NodeRank -> {l:Tick(l':NEWavl) | is2ChildN n (tval l) } -> r:ChildB n  
          -> {v:Tick ({t:NEWavl | right t == r && Is2Child t (tval l) && rk t == n && IsWavlNode t && potT t >= pot1 l + potT r}) | tcost l == tcost v
           }
```