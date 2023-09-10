# Defining the creation of a WAVL Tree anew

I thought by defining the Tree class plus the balanced definition i would be able to cover all cases. But this seemed to be naught, i.e. 
by using this relaxed structure (in comparison to all possible states in a WAVL tree) I found that 
I had to rewrite some of the most basics function I thought LH could come up by itself. 

One of the eye openers where the limits of the framework were, was when I had to follow up on an LH error and trying to find the root cause of it, since the error message wasn't descriptive enough. 

So, when encountering an error, saying that the Tree was not satisfying the notEmpty property in a where clause i came up with the idWavl function: 

```haskell
{-@ idWavl :: x:a -> n:NodeRank -> {l:Wavl | rk l < n && n <= rk l + 2} 
          -> {r:Wavl | rk r < n && n <= rk r + 2 } 
          -> {t:NEWavl | (not (not notEmptyTree l && not notEmptyTree r) || (rk t == rk l + 1 && rk t == rk r + 1 && rk t == 0)) 
                      && ((not notEmptyTree l && not notEmptyTree r)     || (rk t == n && left t==l && right t == r)) } @-}
idWavl :: a -> Int -> Tree a -> Tree a -> Tree a
idWavl x n l r
    | notEmptyTree r = idWavlR x n l r
    | notEmptyTree l = idWavlL x n l r -- notEmptyTree l
    | otherwise = singleton x

{-@ idWavlL :: x:a -> n:NodeRank -> {l:NEWavl | rk l < n && n <= rk l + 2} -> {r:Wavl | rk r < n && n <= rk r + 2 } 
          -> {t:NEWavl | val t == x && rk t == n && left t==l && right t == r } @-}
idWavlL :: a -> Int -> Tree a -> Tree a -> Tree a
idWavlL x n l r = Tree x n l r

{-@ idWavlR :: x:a -> n:NodeRank -> {l:Wavl | rk l < n && n <= rk l + 2} 
          -> {r:NEWavl | rk r < n && n <= rk r + 2 } -> {t:NEWavl | rk t == n && left t==l && right t == r } @-}
idWavlR :: a -> Int -> Tree a -> Tree a -> Tree a
idWavlR x n l r = Tree x n l r
```

## Explanation for idWavl refinement
i.e. we say that each tree created via the Tree constructor is either a
  * 1,1 Node (singleton or with both non-empty children l/r)
  * 1,2 Node (symmetric for l/r)

  non other are allowed. In this function we use the singleton and this raises the problem of non-conform n values, 
  i.e. if n is greater than 0 and both children are NIL then we should reject the input

  **AND**: we actually do. by saying that n has to fall into the range of `rk l < n && n <= rk l + 2` (and symmetrical for r) we constrain n enough
  to satisfy all of our cases except one, i.e. `n == 1 && empty l && empty r`
  In this case we don't reject it but we reduce the value of n by 1, making it 0. This course of reducing a leaf with rank 1 to 0 is also described in the paper [2] and is part of our balanced property for Wavl trees. 

  **REMARK**: this property of constraining leaves to 0 was done by the authors to prevent the need for 2 rotate steps. This scenario could be found in a tree where multiple deletes result in a 2,2-node (leaf) being a child of a 2,2-node. If a deletion took place along this path and the leaf of rk 1 is found to be the predecessor then its parent could become a 4,*-node which could not be repared by a single rotation case.  

# Encountered Problems and why it was necessary to define idWavl

We have to define the creation of a Tree, even when we thought that all constraints were there in some functions, e.g. in insert: 

```haskell
{-@ insert :: (Ord a) => a -> s:Wavl -> t':{Tick ({t:NEWavl | (EqRk t s || RkDiff t s 1) 
          && (not (isNode2_2 t) || (EqRk t s)) 
          && ((not (isNode1_1 t && rk t > 0)) || EqRk t s) && IsWavlNode t }) 
          | tcost t' >= 0 && (not (RkDiff s (tval t') 1) || (potT2 (tval t') + tcost t' <= potT2 s))
                          && (not (EqRk (tval t') s)     || (potT2 (tval t') + tcost t' <= potT2 s + 2))
          }  @-} -- / [rk (tval t')]
insert :: (Ord a) => a -> Tree a -> Tick (Tree a)
insert x Nil = pure (singleton x)
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> insR
    EQ -> pure t
    where
      l' = insert x l
      r' = insert x r
      l'' = tval l'
      r'' = tval r'
      insL | rk l'' < n  = RTick.step (tcost l') (pure (idWavlL v n l'' r))
           | rk l'' == n && rk l'' == rk r + 1 = RTick.step (tcost l' + 1) (pure (promoteL (Tree v n l'' r))) 
           | rk l'' == n = RTick.step (tcost l') (pure (balL v n l'' r)) 
      insR | rk r'' < n  = RTick.step (tcost r') (pure (idWavlR v n l r''))
           | rk r'' == n && rk r'' == rk l + 1 = RTick.step (tcost r' + 1) (pure (promoteR (Tree v n l r''))) 
           | rk r'' == n = RTick.step (tcost r') (pure (balR v n l r''))
```
In this example, LH indicated, that insL and insR respectively were not satisfying the constraint, i.e. being full WAVL trees. 

From the pre-condition one can see that in
```haskell
(promoteL (Tree v n l'' r))
```
has to be WAVL-satisfying, simply because if promoteL accepts this input, then it's output will be a valid `Node1_2` (refinement) type, which itself is a NEWavl/Wavl (refinement) type. 

Cause for concern was the property 

```haskell
{-@ 
...
&& (not (RkDiff s (tval t') 1) || (potT2 (tval t') + tcost t' <= potT2 s))
&& (not (EqRk (tval t') s)     || (potT2 (tval t') + tcost t' <= potT2 s + 2))
@-}
```

which was not a refinement on any of the functions inside of `insert`. On a first (deeper) glance into the function, one would assume again falsely that the underlying SMT solver should be able to see the relation between 

```haskell
tcost (RTick.step (tcost l') _) <=> (potT2 (tval t') + tcost t' <= potT2 s)
```
but this is seemingly to much of a stretch and needs further more explicit refinements on the used modelling parts inside `insert`.
