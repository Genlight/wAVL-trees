in commit 1b9232db7e327e3d4b47d0f9a0331b469d849321 we had the problem, 

that the condition `rk (tval r')` in the function `insert` was not propagated to the expression and we got the LH unsafe message: 
```
Liquid Type Mismatch
.
The inferred type
  VV : {v : (PotentialAnalysis_WAVL.Tree a) | balanced v
                                              && notEmptyTree v
                                              && notEmptyTree v
                                                 || rk v == (-1)
                                              && (notEmptyTree (left v)
                                                  && rk (left v) + 1 == rk v
                                                  && rk (right v) + 2 == rk v)
                                                 || ((notEmptyTree (right v)
                                                      && rk (left v) + 2 == rk v
                                                      && rk (right v) + 1 == rk v)
                                                     || ((notEmptyTree (left v)
                                                          && notEmptyTree (right v)
                                                          && rk (left v) + 2 == rk v
                                                          && rk (right v) + 2 == rk v)
                                                         || (rk (left v) + 1 == rk v
                                                             && rk (right v) + 1 == rk v)))
                                              && not (notEmptyTree v)
                                                 || rk v >= 0
                                              && not (notEmptyTree (left v)
                                                      && notEmptyTree (right v)
                                                      && rk (left v) + 2 == rk v
                                                      && rk (right v) + 2 == rk v)
                                                 || rk r == rk v
                                              && not (rk (left v) + 1 == rk v
                                                      && rk (right v) + 1 == rk v
                                                      && rk v > 0)
                                                 || rk r == rk v
                                              && rk r == rk v
                                                 || rk v - rk r == 1
                                              && ht v >= (-1)
                                              && potT v >= 0
                                              && potT2 v >= 0
                                              && rk v >= (-1)}
.
is not a subtype of the required type
  VV : {VV : (PotentialAnalysis_WAVL.Tree a) | n > rk VV}
.
in the context
  r : {r : (PotentialAnalysis_WAVL.Tree a) | notEmptyTree r
                                             || rk r == (-1)
                                             && not (notEmptyTree r)
                                                || rk r >= 0
                                             && ht r >= (-1)
                                             && potT r >= 0
                                             && potT2 r >= 0
                                             && rk r >= (-1)
                                             && n <= rk r + 3
                                             && rk r <= n}
   
  n : {n : GHC.Types.Int | n >= 0}
Constraint id 175

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

### things i tried

I thought that maybe exchanging `r'` in the `where` clause for a similar `let` construct would give me more control over `r'` constraints but similar issues arise there. 
