# Proving functional invariants of weak AVL trees

I showed via the LiquidHaskell framework that my functional Implementation of the wAVL trees are functional correct for insert (and delete, TODO). 

# Watch out for's of LiquidHaskell

## function annotation

in a function annotation we can use the input to refine the output, and vice versa. Like this: 

```haskell
{-@ merge :: x:a -> l:Wavl -> r:Wavl -> {v:Rank | WavlRankN v l r }  -> t:Wavl @-}
```

But LiquidHaskell will not accept the following and throws an unbound Sort Refinement Error: 
```haskell
{-@ merge :: x:a -> {v:Rank | WavlRankN v l r } -> l:Wavl -> r:Wavl -> t:Wavl @-}
```
This is a LiquidHaskell implementation detail. In a function refinement, if you use a variable like l or r before declaration, it will not be accepted. 




## Special cases because of LiquidHaskell

To show correctness of the insert algorithm with LiquidHaskell I had to make some implicit logical knowledge over the structure explicit. 
E.g. the pattern matching case for the rebalancing in the insert function could look like this: 

```haskell
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> insR
    EQ -> t
    where 
        l' = insert x l
        lt' = Tree v n l' r
        insL | rk l' < n = lt'
             | rk l' == rk r + 1 = promoteL lt'
             | (rk (left l') + 1) == rk l' = rotateRight lt' 
             | otherwise = rotateDoubleRight lt' 
```

but because we need to make sure that the input to the functions of rotateRight / rotateDoubleRight is "filtered", i.e. the logical condition is used to show that this branch only gives over the correct refined lt', so that it satisfies their type annotations. 

```haskell
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> insR
    EQ -> t
    where 
        l' = insert x l
        lt' = Tree v n l' r
        insL | rk l' < n = lt'
             | rk l' == n && rk l' == rk r + 1 = promoteL lt'
             | rk l' == n && rk l' == rk r + 2 && (rk (left l') + 1) == rk l' && (rk (right l') + 2) == rk l' && notEmptyTree (left l') = rotateRight lt' 
             | rk l' == n && rk l' == rk r + 2 && (rk (right l') + 1) == rk l' && (rk (left l') + 2) == rk l' && notEmptyTree (right l') = rotateDoubleRight lt' 
             | otherwise = t
...
```

with our (implicit) knowledge over the data structure we know that the otherwise case will never execute. this is because the input to insert will always be a legitimate wAVL tree, which is defined via the balanced condition: 

```haskell
{-@ type Wavl = {v: Tree a | balanced v} @-}

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced Nil = True
balanced t@(Tree _ n l r) = rk r < n && n <= rk r + 2 
                         && rk l < n && n <= rk l + 2
                         && (balanced l)
                         && (balanced r)
```

Therefore, we know that a tree under insertion will sat. these conditions beforehand. During the insertion there can be only one violation of this, namely that there is a Node with a 0-child, i.e. a 0,1-Node or a 0,2-Node respectively. These two cases are pattern matched, while 0,2-Nodes are further checked whether the right or left child node of l' (or respectively r' in mirror case insR) fulfills the condition of being the one node where the further down insertion took place. 

Also, LH cannot infer that another case will not be accessed, namely what happens if we encounter a 0,2-Node with a left child, which is a 1,1-Node?
Well, this cannot happen. Since via the insertion we could create a single 0-Child, this will stay the only violation in the data structure. The violation is then being moved up via a promote step, leaving a 1,2-Node behind. So in order for an execution of rotate* or doubleRotate* we know that the structure of the underlying tree must have been created by 1 or more promote steps. Nothing else would create a violation of the balanced constraint and we would only return the new tree as a result of the first pattern in insL. 

Thus, we know that l' must be either a 1,2-Node or 2,1-Node, because a 1,1-Node couldn't be produced by a previous promote step. If a 1,1-Node was created through the insertion, the said Node would have to been either a 1,2-Node, and promotion would make the 2-child to a 1-child. But this would not change the rank of the bespoken node itself and thus the rank violation is corrected. 

the last case of l' being a 2,2-node can be disregarded since then the node would have been a 2,3-Node before the insertion, which is not possible since we only insert into balanced wAVL trees. 

thus, our pattern matching cases are legit but LH cannot infer this on it's own. 

A last notion: the `otherwise` case will also not be executed but is needed to tell LH that all patterns are matched. To prove that this case is never executed we just need to look again at the insertion path and in what states a node could be in along this path. 

Either a rank violation in form of a 0-child is carried along and the first pattern does not match. In that case, one of the other three cases will definitely execute as shown above. Otherwise, the first pattern will match since after a "terminal" rotation or promotion step the tree will be balanced totally, since there will always only be one violation be introduced via insertion and carried upwards along the insertion path. 

Thus, we have shown that every possible case in the recursion is matched and the otherwise operation will not execute. 





