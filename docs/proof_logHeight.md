# Unused lemmas

```haskell
{-@ lemma_05 :: { t:Wavl2_2 | rk t >= 2} -> { v:Wavl2_2 | rk v == rk t} -> {sum t + sum v == 2 * sum t } @-}
lemma_05 :: Tree a -> Tree a -> ()
lemma_05 t v =  sum t + sum v ? lemmaSubSum t v 
            === sum t + sum t 
            === sum t * 2 
            *** QED
```

```haskell
{-@ lemma_02 :: n:Int -> {(div n 2) + 1 == (div (n + 2) 2)} @-}
lemma_02 :: Int -> ()
lemma_02 n = (div n 2) + 1 === (div n 2) + (div 2 2) ? ()
                           === div (n + 2) 2 *** QED
```