
# Problem Description to WAVL trees and the BAlDel method 


In my tries to find suitable refinements I often looked at the test files for LiquidHaskell, espec. at [AVL.hs](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/tests/pos/AVL.hs). 

that is also the reason why some of the function names sound very similar and the insert function looks very similar to your code. 

Reason is that my first runs with LiquidHaskell did not prove fruitful and I tried to understand it by incrementally changing your code to the WAVL algorithm. 

## Concrete Problem:
In [WAVL.hs](src/WAVL.hs), on line 206, I get an error regarding the expression: 

```haskell
... notEmptyTree r && (notEmptyTree (left r)) && (notEmptyTree (right r)) && ...
```

The error message states that r needs a refinement predicate of notEmptyTree in order to be used with left/right.  

As I understand it, LiquidHaskell recognizes that `r` has a refinement, namely being a WAVL tree, getting it from the function refinement `balLDel`.

Now, my problem with this is that I expected it / LH to realize that in order to fulfill the constraint r needs to sat. the condition of being not an empty tree. Otherwise the constraint for that line would not have been satisfied and we can skip it.

I cannot include the notEmptyTree predicate at function refinement level for r at `balLDel` because I also need to accept empty trees. 

Is there some other way to propagate the predicates inside a function?

# Problem solution
After an email correspondence with [Ranjit Jhala](https://github.com/ranjitjhala), one of the core developers of LiquidHaskell, I added a crude solution with the last WIP [commit](https://github.com/Genlight/lhTest/commit/373be42d37f3508039555e65c66e3938470d80b1).

Solution was to add another function, add a precondition in balDelL for `notEmptyTree r` and put that into the function refinement for that sub function. While the function refinement for the sub stayed the same as for `balDelL` I added a notEmptyTree r to it which LH accepted.  