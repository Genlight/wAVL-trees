# Problem

LH is not able to (implicitly) prove the statement 
```
Wavl \suptype AlmostWavl
```

The step from `t:Tree a | balanced t` to `Tree a | balanced (left t) && balanced (right t)` could not be resolved. 

Here, we find again an issue with the notemptyTree t situation, i.e. a WAVL tree can be empty but an AlmostWavlTree can't. So, even if we have the constraint of `Wavl | notEmptyTree` we find that LH does not see that such a construct also satisfies `AlmostWavl`.

Explanation: Similar to the Proof from WavlNode to Wavl we find that there are more than one step which PLE can overcome, i.e. we need to show that the left and right tree are balanced by using the definition of `balanced`.