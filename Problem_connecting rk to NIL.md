After some trial and error I found that with the function `rotateDoubleLeftD` I was missing a logical connection between the rank of a tree and whether it is Nil or not. 

First, I was confused by that, because previously this asssumption held for me, or so I thought. 

What was actually true was the implication: an empty Tree (Nil) implied a rank of `-1` and a non-empty Tree a rank greater than that but the same implication was not proven for the other direction. 

So, when I tried to establish relation between Trees in a refinement using ranks the pattern matching of LH said I was missing something. 

Only when I used an implication of the NIL state LH said it was "safe". 

The concrete function I tried to refine:

```haskell
{-@ rotateDoubleLeftD :: {s:Node3_1 | notEmptyTree (right s) && notEmptyTree (left (right s)) && IsNode1_2 (right s) 
                        && (not (notEmptyTree (right s) || (notEmptyTree (right (right s)) ))) } -- <-- this was the accepted term
-> {t:Wavl | EqRk s t && notEmptyTree t} @-}
rotateDoubleLeftD :: Tree a -> Tree a
-- rotateDoubleLeftD (Tree z 2 Nil (Tree y m (Tree v o _ _) _)) = Tree v 2 (singleton z) (singleton y)
rotateDoubleLeftD (Tree z n x (Tree y m (Tree v o vl vr) yr)) = Tree v n (Tree z (n-2) x vl) (Tree y (n-2) vr yr)
```

and the not eaccepted term: 

```haskell
{-@ rotateDoubleLeftD :: {s:Node3_1 | notEmptyTree (right s) && notEmptyTree (left (right s)) && IsNode1_2 (right s) 
                        && rk (right s) == rk (right (right s)) } -- <-- unsafe term
-> {t:Wavl | EqRk s t && notEmptyTree t} @-}
rotateDoubleLeftD :: Tree a -> Tree a
-- rotateDoubleLeftD (Tree z 2 Nil (Tree y m (Tree v o _ _) _)) = Tree v 2 (singleton z) (singleton y)
rotateDoubleLeftD (Tree z n x (Tree y m (Tree v o vl vr) yr)) = Tree v n (Tree z (n-2) x vl) (Tree y (n-2) vr yr)
```

While the first is not straight forward, it is actually the implication if x is not Nil so must be yr. Actually, this is an equivalence but LH accepted it with only the one direction. 

My realization from that: 

what I thought already to be explicit and "connected" through logic wasn't.
