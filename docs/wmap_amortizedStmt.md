# Proving the amortized statement

we want to proof the following amortized statement for the insert function: 
```haskell
{-@ inline amortizedStmt @-}
{-@ amortizedStmt :: Tick (Wavl) -> Wavl -> Bool @-}
amortizedStmt :: Tick (Tree a) -> Tree a -> Bool
amortizedStmt t' s = (not (rkDiff s (tval t') 1) || amortized t' s)
                 && (not (eqRk (tval t') s)     || amortized1 t' s)
```

With EqT / EqT1 and EqT2 as our respective type refinements for the different state transitions (i.e. from Tree to Tree / Tree to Tick / Tick to Tick as the resp. top-most type annotation) we face the problem that the refinements worked out and LH told us it would be safe to use them but we also wrote this: 
```haskell
-- use only for promoteL
{-@ wmapPromL :: f:PromoteL_t
          -> {s:Tick (Node0_1) | tcost s >= 0} 
          -> {t':EqT2 s | Tick (tcost s + 1) (f (tval s)) == t' && RkDiff (tval t') (tval s) 1} @-}
wmapPromL :: (Tree a -> Tree a) -> Tick (Tree a) -> Tick (Tree a)
wmapPromL f (Tick m x) = undefined -- Tick (1 + m) (f x) 
```

with: 

```haskell
{-@ type PromoteL_t = (t1:Node0_1 -> {t:EqT1 t1 | IsNode1_2 t && RkDiff t t1 1 && potT2 t1 -1 == potT t} ) @-}
{-@ promoteL :: PromoteL_t @-}
promoteL :: Tree a -> Tree a
promoteL (Tree a n l r) = (Tree a (n+1) l r)
```

Problem: LH cannot tell that the input f satisfies the `amortizedStmt` or not. the `undefined` circumvents the problem by telling LH that the function is `safe` and not to be checked. 

We know that only `amortizedStmt` is not provable in this stage. 

How are we using the propositions and how are they related to each other? 

The transistions (relating the output from the sub functions to the output of the parent function) are like this: 
| promoteL     | wmapPromL          | insert |
| -------------| ------------------ | ------ |
| `PromoteL_t` | `f:PromoteL_t`     |   -    |
| `EqT1` (Tree-Tree, no `amortizedStmt`) | `EqT2` (Tick-Tick) | `EqT` (Tree-Tick) |
| `RkDiff t t1 1` | `RkDiff (tval t') (tval s) 1` | `(EqRk t s \|\| RkDiff t s 1)` (in `EqT`)|
| `potT2 t1 -1 == potT t` | - | - |
| - | `amortizedStmt t' (tval s)` | `amortizedStmt t' s` |

the amortized Statement, i.e. `amortizedStmt`, is build like this, written out: 
```haskell
amortizedStmt t' s = (not (rkDiff s (tval t') 1) || pot1 t' + tcost t' == potT s)
                  && (not (eqRk (tval t') s)     || pot1 t' + tcost t' <= potT s + 2)

```

## conclusion
I found that one of my statements doesn't hold in wmpa_promoteL, namely EqT2. The problem lies with the amortized statement bc it leaves out `tcost` for the input variable.

What I originally had: 
```haskell
type EqT2 = ... amortizedStmt t' (tval s)

-- and

amortized t' s = pot1 t' + tcost t' == potT s
```

which is essentially false, because it only is valid for the insert statement, but not the recursive step:
```haskell
amortized' t' s = pot1 t' + tcost t' == potT1 s + tcost s
```

Thus, we updated `amortizedStmt` to the following: 
```haskell
{-@ inline amortizedStmt @-}
{-@ amortizedStmt :: Tick (Wavl) -> Wavl -> Bool @-}
amortizedStmt :: Tick (Tree a) -> Tree a -> Bool
amortizedStmt t' s = (not (rkDiff s (tval t') 1) || amortized t' (pure s))
                 && (not (eqRk (tval t') s)     || amortized1 t' (pure s))
```

and

```haskell
{-@ inline amortized @-}
{-@ amortized :: Tick (Wavl) -> Tick (Wavl) -> Bool @-}
amortized :: Tick (Tree a) -> Tick (Tree a) -> Bool
amortized t' s = pot1 t' + tcost t' <= pot1 s + tcost s
-- amortized t' s = pot1 t' + tcost t' <= potT s

{-@ inline amortized1 @-}
{-@ amortized1 :: Tick (Wavl) -> Tick (Wavl) -> Bool @-}
amortized1 :: Tick (Tree a) -> Tick (Tree a) -> Bool
amortized1 t' s = pot1 t' + tcost t' <= pot1 s + tcost s + 2
```

## insert: trying to assert which applies
By trying out which constraints LH can actually infer I found that with commit `9e0041289787d3787cff56a941129c639f29b82a (HEAD -> test/wmap, origin/test/wmap)`
we found that at the insert function at the insL level was not able to infer the node structure before an insert in one of the child nodes. 

```haskell
insert x t@(Tree v n l r) = 
...
     insL | rk (tval l') < n                       = undefined -- treeLW1 v n l' r -- assert (amortized1 l' l) ?? (treeL v n l' r) -- is not accepted
              
            | is0ChildN n l'' && rk l'' == rk r + 1 && n == 0 = assert (not (notEmptyTree l)) ?? assert (not (notEmptyTree r)) ?? 
             assert (potT l == 0) ?? -- fails to prove!!
             assert (potT r == 0) ?? -- fails to prove!!
             assert (0 == potT t) ?? -- fails to prove!!  
           | is0ChildN n l'' && rk l'' == rk r + 1  =  assert (n == rk (tval l')) ??
              assert (n == rk r + 1) ?? 
              assert (n >= 0) ?? 
              assert (rk (tval (Tick (tcost l') (Tree x n (tval l') r))) == n) ??
              assert (rk (tval (Tick (tcost l') (Tree x n (tval l') r))) == rk r + 1) ??
              assert (rk (promoteL (tval (Tick (tcost l') (Tree x n (tval l') r)) )) == rk r + 2) ?? 
              assert (rk (promoteL (tval (Tick (tcost l') (Tree x n (tval l') r)) )) == rk (tval l') + 1) ?? 
              assert (rk (promoteL (tval (Tick (tcost l') (Tree x n (tval l') r)) )) == n + 1) ?? 
              assert (rk (tval (wmap promoteL (Tick (tcost l') (Tree x n (tval l') r)) )) == n + 1) ?? -- fails to prove !! 
              assert (rk (tval (wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r)) )) == n + 1) ?? 
              assert (isNode1_1 t ) ?? 
              assert (rk (tval (wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r)) )) == n + 1) ??
              assert (isAlmostWavl (tval (Tick (tcost l') (Tree x n (tval l') r)))) ??
              assert (amortized l' (pure l)) ??
              assert (potT l'' + potT r + 1 == potT2 (Tree x n (tval l') r)) ??
              assert (potT l'' + potT r == potT (tval (wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r) )))) ??
              assert (potT l'' + potT r + tcost l' <= tcost (wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r))) + potT (tval (wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r) )))) ?? --not important, the next one is
              assert (potT l'' + potT r + tcost l' + 1 == tcost (wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r))) + potT (tval (wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r) )))) ??
              assert (potT t >= potT r + potT l) ??
              assert (potT t >= potT r + potT l'' + tcost l') ??
              assert (potT l + potT r + 1 == potT t) ?? -- fails to prove
              assert (potT (tval (wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r) ))) + tcost (tval (wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r) ))) <= potT t) ?? -- fails to prove
              wmapPromL promoteL (Tick (tcost l') (Tree x n (tval l') r) )
```

Thus the same should apply for all other rotations / steps, i.e. we only check for structure after the application

## found problem

there is the case with `n=0` | `isNode1_1 t` which results in `potT t = 0` and `potT t == potT r + potT l`, i.e. the insertion of a node can create potential, in the step right after the singleton case. 

# Solution

analog to treeLW1 using case distinctions, i found that i could define two sub-functions, i.e. `wmapPromL_1` and `wmapPromL_2` and that worked out. 
But now i have a more complex input type for `wmapPromL` which may not work with the refinements in `insert`.

# new Problem, at insert level
node1-1-Stmt needs a change in the balanced definition or i need to redefine `wmapPromL`.