# using the new common potT with insert
I tried to annotate insert with the proposed annotation, i.e. differentiating the two cases: 
```haskell
{-@ insert :: (Ord a) => a -> s:Wavl -> t':{Tick ({t:NEWavl | (EqRk t s || RkDiff t s 1) 
          && (not (isNode2_2 t) || (EqRk t s)) 
          && ((not (isNode1_1 t && rk t > 0)) || EqRk t s) && IsWavlNode t }) 
          | tcost t' >= 0  
          && (not (RkDiff (tval t') s 1) || 
            ((potT2 (tval t') + tcost t' <= potT2 s) && (potT (tval t') + tcost t' <= potT s))
          )
          && (not (EqRk (tval t') s)     || 
            ((potT (tval t') + tcost t' <= potT s + 3) && (potT (tval t') + tcost t' <= potT s + 3))
          )
          } @-}
```

but LH returned the following error message: 
```bash
The inferred type
  VV : {v : (Language.Haskell.Liquid.RTick.Tick (PotentialAnalysis_WAVL.Tree a)) | v == insL}
.
is not a subtype of the required type
  VV : {VV : (Language.Haskell.Liquid.RTick.Tick {VV : (PotentialAnalysis_WAVL.Tree a) | balanced VV
                                                                                         && notEmptyTree VV
                                                                                         && (notEmptyTree (left VV)
                                                                                             && rk (left VV) + 1 == rk VV
                                                                                             && rk (right VV) + 2 == rk VV)
                                                                                            || ((notEmptyTree (right VV)
                                                                                                 && rk (left VV) + 2 == rk VV
                                                                                                 && rk (right VV) + 1 == rk VV)
                                                                                                || ((notEmptyTree (left VV)
                                                                                                     && notEmptyTree (right VV)
                                                                                                     && rk (left VV) + 2 == rk VV
                                                                                                     && rk (right VV) + 2 == rk VV)
                                                                                                    || (rk (left VV) + 1 == rk VV
                                                                                                        && rk (right VV) + 1 == rk VV)))
                                                                                         && not (notEmptyTree (left VV)
                                                                                                 && notEmptyTree (right VV)
                                                                                                 && rk (left VV) + 2 == rk VV
                                                                                                 && rk (right VV) + 2 == rk VV)
                                                                                            || rk ?a == rk VV
                                                                                         && not (rk (left VV) + 1 == rk VV
                                                                                                 && rk (right VV) + 1 == rk VV
                                                                                                 && rk VV > 0)
                                                                                            || rk ?a == rk VV
                                                                                         && rk ?a == rk VV
                                                                                            || rk VV - rk ?a == 1}) | rk (tval VV) - rk ?a == 1
                                                                                                                      || potT (tval VV) + tcost VV <= potT ?a + 3}
.
in the context
  insL : (Language.Haskell.Liquid.RTick.Tick (PotentialAnalysis_WAVL.Tree a))
   
  ?a : {?a : (PotentialAnalysis_WAVL.Tree a) | balanced ?a
                                               && notEmptyTree ?a
                                                  || rk ?a == (-1)
                                               && not (notEmptyTree ?a)
                                                  || rk ?a >= 0
                                               && ht ?a >= (-1)
                                               && rk ?a >= (-1)}
Constraint id 1421
```

it seems to me that LH loses / drops some information during his check. Here, i refer to the part about the "inferred type", where LH cannot infer that the returned tree from insL is also a "balanced" Tree, in fact a WAVL tree. Without the last added clause about the potential (s. Remark) it works and LH can indeed infer that any other statement about this is correct. 

So, without the WAVL tree clauses we get: 
```bash
The inferred type
  VV : {v : (Language.Haskell.Liquid.RTick.Tick (PotentialAnalysis_WAVL.Tree a)) | v == insL}
.
is not a subtype of the required type
  VV : {VV : (Language.Haskell.Liquid.RTick.Tick {VV : (PotentialAnalysis_WAVL.Tree a) | ... | rk (tval VV) - rk ?a == 1
                                                                                              || potT (tval VV) + tcost VV <= potT ?a + 3}

```

So it seems we only need to rethink about how to insert the last added potential correctly.

### Ideas & Thoughts
My thoughts circle around the `tcost VV` and `tval VV` terms. `tcost VV` bc we haven't set an upper constraint on how large it can become. Thus this term can be interpreted as way bigger than it is implied by us. 

`tval VV` bc we could have again similar problems we had like in the beginning using the RTick module, s. the [Problem description_Tick.md]


## Remark: the last added potential 
is this one:
```haskell
&& (not (RkDiff (tval t') s 1) || 
            ((potT2 (tval t') + tcost t' <= potT2 s) && (potT (tval t') + tcost t' <= potT s))
          )
          && (not (EqRk (tval t') s)     || 
            ((potT (tval t') + tcost t' <= potT s + 3) && (potT (tval t') + tcost t' <= potT s + 3))
          )
```