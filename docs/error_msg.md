```bash
Liquid Type Mismatch
.
The inferred type
  VV : {v : (Language.Haskell.Liquid.RTick.Tick (PotentialAnalysis_WAVL.Tree a)) | v == insL}
.
is not a subtype of the required type
  VV : {VV : (Language.Haskell.Liquid.RTick.Tick {v : (PotentialAnalysis_WAVL.Tree a) | balanced v
&& notEmptyTree v
&& (notEmptyTree (left v)
   && rk (left v) + 1 == rk v
   && rk (right v) + 2 == rk v)
   || ((notEmptyTree (right v)
      && rk (left v) + 2 == rk v
      && rk (right v) + 1 == rk v)
      || ((notEmptyTree (left v)
            && notEmptyTree (right v)
            && rk (left v) + 2 == rk v
            && rk (right v) + 2 == rk v)
         || (rk (left v) + 1 == rk v
               && rk (right v) + 1 == rk v)))
&& not (if not (notEmptyTree ?a) then false else rk (left ?a) + 2 == rk ?a
&& (rk (right ?a) + 2 == rk ?a
&& (notEmptyTree (right ?a)
      && notEmptyTree (left ?a))))
   || rk ?a == rk v
&& not (notEmptyTree (left v)
      && notEmptyTree (right v)
      && rk (left v) + 2 == rk v
      && rk (right v) + 2 == rk v)
   || rk ?a == rk v
&& not (rk (left v) + 1 == rk v
      && rk (right v) + 1 == rk v
      && rk v > 0)
   || rk ?a == rk v
&& rk ?a == rk v
   || rk v - rk ?a == 1}) | not (rk (tval VV) - rk ?a == 1)
                           || potT (tval VV) + tcost VV == potT (tval (pure ?a)) + tcost (pure ?a)}
.
in the context
  insL : (Language.Haskell.Liquid.RTick.Tick (PotentialAnalysis_WAVL.Tree a))
   
  ?a : {?a : (PotentialAnalysis_WAVL.Tree a) | balanced ?a
                                               && notEmptyTree ?a
                                                  || rk ?a == (-1)
                                               && not (notEmptyTree ?a)
                                                  || rk ?a >= 0
                                               && ht ?a >= (-1)
                                               && potT ?a >= 0
                                               && potT2 ?a >= 0
                                               && rk ?a >= (-1)}
Constraint id 35
```