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

