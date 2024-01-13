
# at insert
This implication tells you that an output node of rank 0 can only have an amortized cost. 

```haskell
(rk (tval t') > 0 || amortized t' (pure s))
```

# amortized Statement
Problem: it fails currently with only treeLW1 added in the mix bc LH does not see it as safe w/o it: 

```haskell
{-@ inline amortizedStmt @-}
{-@ amortizedStmt :: Tick (Wavl) -> Wavl -> Bool @-}
amortizedStmt :: Tick (Tree a) -> Tree a -> Bool
amortizedStmt t' s = (not (rkDiff s (tval t') 1) || amortized1 t' (pure s))
                 && (not (eqRk (tval t') s)      || amortized3 t' (pure s))
                --  && (rk (tval t') == 0 || amortized  t' (pure s)) -- same as s == Nil, maybe needed in wmapProml case
```

This 2nd case can probably be solved with a refinement for `potT`. 