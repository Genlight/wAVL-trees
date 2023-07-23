# Problem description: Reflecting functions into LH logic

During my trials do prove theorem 4.3 I found I couldn't reflect the balancing function `balRDel'` into the LH logic. the error messages were cryptic 
and they pointed me to functions I could separate from the rest of my code and reflect them without any issues. So, after some trial & error I found out that 
in order for functions with multiple cases like this: 

```haskell
{-@ reflect balS' @-}
{-@ balS' :: a -> n:NodeRank -> {l:MaybeWavlNode' | Is2ChildN n l} -> {r:Tick ({r':Wavl' | Is2ChildN n r'}) | tcost r >= 0 } -> Tick ({t:NEWavl' | (rk t == n || rk t + 1 == n) }) @-}
balS' :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
balS' x n l r | not (notEmptyTree l) && not (notEmptyTree (tval r)) = RTick.step (tcost r) (pure (singleton x))
              | n <  rk (tval r) + 3 = (pure (Tree x n l (tval r)))
              | n == rk (tval r) + 3 && rk l + 2 == n = RTick.fmap demoteR ((pure (Tree x n l (tval r))) ) -- amort. cost 0
              | n == rk (tval r) + 3 && rk l + 1 == n && rk (left l) + 2 == rk l && rk (right l) + 2 == rk l = RTick.fmap doubleDemoteR ((pure (Tree x n l (tval r))) ) -- same
              ....
            
```

I needed to add one last case, namely an `otherwise` case to satisfy LH (even if this otherwise case will never be called in my function logic).

IMO the problem or the issue LH developers saw with such a reflection is that the function in question is *unchecked* and will be lifted into the logic. So, in order to implement some safe guards one of the hurdles /checks to insure users don't shoot themselves into the foot by reflecting anything, they should provide well-covered case distinctions for their functions. (note: this is just my interpretation on how LH reacted to different input)

This "*feature*" of LH is IMO undocumented in that sense it isn't mentioned in the Spec reference of the reflection, at. Also, I didn't find it anywhere else in the documentation or blog entries. 

## solution

instead of the rather meaningless error message: 

```bash
[2 of 2] Compiling PotentialAnalysis_WAVL

<no location info>: error:
    • Uh oh.
    src/myHaskellFile.hs:137:13 Cannot lift Haskell function `balS'` to logic
                                         checkBoolAlts failed on [(GHC.Types.True,
  [],
  Language.Haskell.Liquid.RTick.fmap
    WAVL.rotateDoubleRightD
    (Language.Haskell.Liquid.RTick.pure
       (WAVL.Tree x n l (Language.Haskell.Liquid.RTick.tval r))))]
```

you could describe the error a bit more, like telling the user that reflect needs for this special case an `otherwise` matcher. 

## github issue reported

s. https://github.com/ucsd-progsys/liquidhaskell/issues/2161