# otherwise Problem bei case matching Szenarien with LH

I based my original code on the AVL code (see [./src/AVL.hs](https://github.com/Genlight/lhTest/blob/main/src/AVL.hs). The AVL insert method used an otherwise expression which I copied. Originally, It seemed nice and comfortable, and I also used it in previous attempts at Haskell so I knew the basic functionality. 

But with LH annotations the problem of pattern matching needs becomes apparent: In my algorithm, when I want to show that my BST only needs the following rebalancing operations and otherwise return then I could potentially use this method. But what I want to say is that

what is more intuitive with vanilla haskell became quit unnerving with LH.

For the function balLDel my i had to specify all possible patterns and could not default to the otherwise case as i did in the insert method. 
I found a way in a sense that i specified each possible case a Node could be in and used that collection of possible cases in the annotation, s.t. to not pollute the code any further (see my type annotation "MaybeWavlNode" in [./src/Wavl.hs](https://github.com/Genlight/lhTest/blob/main/src/WAVL.hs). 

From there I found one problem very challenging, namely that LH could not expand on my pattern matching. 

My original idea of the delete function (see file [Wavl.hs](https://github.com/Genlight/lhTest/blob/main/src/WAVL.hs), line 208): 

```haskell
-- Deletion functions
{-@ delete :: (Ord a) => a -> s:Wavl -> {t:Wavl | (EqRk s t) || (RkDiff s t 1)} @-}
delete _ (Nil _) = nil
delete y (Tree x n l r)
  | y < x     = balLDel x n l' r
  | x < y     = balRDel x n l r'
  | otherwise = merge y l r n 
    where
      l' = delete x l
      r' = delete x r
```

what LH in the end accepted: 
```haskell
-- Deletion functions
{-@ delete :: (Ord a) => a -> s:Wavl -> {t:Wavl | (EqRk s t) || (RkDiff s t 1)} @-}
delete _ (Nil _) = nil
delete y (Tree x n l@(Nil _) r@(Nil _))
  | y < x     = balLDel x n l' r
  | x < y     = balRDel x n l r'
  | otherwise = merge y l r n 
    where
      l' = delete x l
      r' = delete x r
delete y (Tree x n l@(Nil _) r@(Tree _ _ _ _))
  | y < x     = balLDel x n l' r
  | x < y     = balRDel x n l r'
  | otherwise = merge y l r n 
    where
      l' = delete x l
      r' = delete x r
delete y (Tree x n l@(Tree _ _ _ _) r@(Nil _))
  | y < x     = balLDel x n l' r
  | x < y     = balRDel x n l r'
  | otherwise = merge y l r n 
    where
      l' = delete x l
      r' = delete x r
delete y (Tree x n l@(Tree _ _ _ _) r@(Tree _ _ _ _))
  | y < x     = balLDel x n l' r
  | x < y     = balRDel x n l r'
  | otherwise = merge y l r n 
    where
      l' = delete x l
      r' = delete x r
```

A possible solution for LH could be that we specify more concrete on which terms we want a case expansion. Maybe there is already a feature like that in the framework and I haven't found it yet but this case expansion is reeeeeeally messy.
