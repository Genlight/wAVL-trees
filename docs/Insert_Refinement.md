---
output:
  pdf_document:
    fig_caption: yes
header-includes:
  \usepackage{float}
  \floatplacement{figure}{H}
  \usepackage[]{algorithm2e}
  \usepackage{amsmath}
  \usepackage{tikz}
  \usepackage{xcolor}
---


# refining the insert function

In the early drafts of writing up the code for the functional implementation of the wavl tree,
I used a different implementation of the insert function, i.e. at first I used a fork of the implementation
in here: (TODO: insert AVL.tree testcase of LH impl)

During my trial & errors with LH I found that the original implementation had a weakness, namely that it included a
`otherwise` expression in its pattern matching. 

It seems innocent at first but LH would reject the refined type for it without it. What LH actually tells us here is thta there exist cases which are not covered by either the refinement (i.e. input constraint) or the patterns written down. 

So, we decided to leave the function at first, as it was but it came back to us. Namely, during the development of my potential analysis or better said the refinement of our functions to prove the potential analysis of [WAVL Tree] theorem 4.1 and 4.2. 

The problem was that LH wasn't able to just prove my assumption on the potential change. So, the failed first attempt looked like this: 

(TODO  insert code snippet: first draft insert refinement)

What I found out was, that LH couldn't prove all the possible cases. In order to constrain the system to a point where it actually could prove it, i refactored the balancing cases into a similar function as I had with the delete case: 


(TODO  insert code snippet: balL)

With a symmetric case for the right side.

So, now our simplified insert looked like this: 

(TODO  insert code snippet: insert with balL)

The same reasoning why I use two bal functions instead of one applies here for the same reason as with the delete cases because it gives me the possibility to refine the allowed cases more in detail for all possible rebalancing steps.



TODO: blablabla


## Defining concrete clauses over possible states

TODO: blablabla
$$
\phi: (\neg (\text{RkDiff t s 1} \wedge \text{rk t} > 0) 
\vee \text{isNode1\_2 t} 
\vee \text{isNode2\_1 t}) 
$$

$$
\phi \Leftrightarrow \\
\neg (\text{RkDiff t s 1}) \vee \neg (\text{rk t} > 0)
\vee \text{isNode1\_2 t} 
\vee \text{isNode2\_1 t} \Leftrightarrow \\

(\text{RkDiff t s 0}) \vee (\text{rk t} \le 0)
\vee \text{isNode1\_2 t} 
\vee \text{isNode2\_1 t} \\
$$

HT: counterexample exist i.e. some state sat. negation of $\phi$. ->

$$
\neg \phi \Leftrightarrow \\
\neg ((\text{RkDiff t s 0}) \vee (\text{rk t} \le 0)
\vee \text{isNode1\_2 t} 
\vee \text{isNode2\_1 t}) \Leftrightarrow \\

\neg (\text{RkDiff t s 0}) \wedge \neg (\text{rk t} \le 0)
\wedge \neg (\text{isNode1\_2 t}) 
\wedge \neg (\text{isNode2\_1 t}) \Leftrightarrow \\
$$

d. h. auch, dass es ein Environment $\mathcal{I}$ gibt, für das gilt: 

$$
1. \mathcal{I} \models \neg  (\text{RkDiff t s 0}) \\
2. \mathcal{I} \models \neg  (\text{rk t} \le 0) \\
3. \mathcal{I} \models \neg  (\text{isNode1\_2 t})  \\
4. \mathcal{I} \models \neg  (\text{isNode2\_1 t})  \\
5. \mathcal{I} \models (\text{RkDiff t s 1}) \quad [\text{1., prop. of insert}]  \\
6. \mathcal{I} \models (\text{rk t} > 0) \quad [\text{2., int}] \\
7. \mathcal{I} \models (\text{isNode1\_1 t}) \vee (\text{isNode2\_2 t}) \quad [\text{3., 4., WAVL balancedness, insert output is NEWavl, MP}] \\
8. \mathcal{I} \not \models (\text{isNode2\_2 t}) \quad [\text{5., prop. of insert, MT}] \\
9. \mathcal{I} \models (\text{isNode1\_1 t}) \quad [\text{7., 8., MP}] \\
$$

Damit erhalten wir für $\mathcal{I}$: 
$\mathcal{I} \models \text{isNode1\_1 t} \wedge (\text{RkDiff t s 1}) \wedge (\text{rk t} > 0)$

Wir haben zwei Zustände bei insert, in welchen die Funktion einen tree mit der Eigenschaft $\text{isNode1\_1 t}$ zurückgibt: 
* Direkt nach dem Einfügen des neuen Nodes, nach dem Aufruf von `singleton x`, wobei hier gilt: $(\text{rk t} == 0)$, somit ist dieser Fall ausgeschlossen und es ist kein CE zu finden. 
* Der Output von `balL` bzw. `balR` nach einem rotate-case. Jedoch erfüllen beide rotation-cases den Zustand: $(\text{RkDiff t s 0})$. Somit gilt auch hier: $\mathcal{I} \not \models balL t$ und selbes für den symmetrischen case
* Der Fall in insL, wobei `rk l' < n` wird nicht modelliert, da $(\text{RkDiff t s 0})$ gilt.
* promote-case: `promote` gibt nur 1,2-Nodes für t zurück, nicht aber 1,1. somit ist auch dieser Fall nicht modelliert. 

Somit gilt $\mathcal{I} \models \bot$ und die HT ist damit widerlegt. Somit ist $\phi$ valid für insert. 


# potT refinement annotation zu insert

das refinement von insert soll die folgende Gleichung enthalten: 

$$
\sum_{i=0}^n c_i \le \sum_{i=0}^n a_i
$$

umgeschrieben: 

$$
\sum_{i=0}^n c_i \le \sum_{i=0}^n (c_i + \Phi_i - \Phi_{i-1}) \\
\sum_{i=0}^n c_i \le \sum_{i=0}^n (c_i) + \Phi_n - \Phi_{0} \\
\sum_{i=0}^n c_i \le \sum_{i=0}^n (c_i) + \Phi_n \\
$$

mit:
* _n_ ... Anzahl der Rebalancing steps
* _t_ ... Baum 


wobei wir wissen, dass n durch den rank von dem INput (Tree t) gebunden ist: $n <= \text{rk }t$

Formel, mit der ich es versucht habe: 

```haskell
... t':Tick ({t:NEWavl | ... }) |
... && (potT (tval t') + tcost t' <= potT s + 3)
``` 

Jedoch schafft LH es nicht von selbst, diesen Umstand zu beweisen. 

## Further cases which are (trivially) true
but strengthen our refinement: 

### Clause 'isNode2_2nNil t $==>$ EqRk t s'
if t is a 2,2-node then we know that the input tree has to have equal rk. The constraint `not Nil` is added because the input tree s could be Nil thus not be a 2,2-Node. Therefore we refined this constraint in order to only affect 2,2-nodes. 

#### proof
Trivially true because s is a Wavl tree and if after an insert t is a 2,2-Node no promote step was done in the step right before. The only step who returns a 2,2-node is the rebuilding (i.e. treeW) case and this one always has the same rank. 

# insert comments(moved from code): 
```haskell
{-- insert x t = c is
  2,2 -> must be EqRk, since this case isn't produced from bal*, therefore -> (isNode2_2 c) -> EqRk c t
  1,2 || 2,1  -> can be either a case "after" rebalancing or be a promote step but also for a promote step
  1,1:  can have different causes, but for all cases it is true that: (rk c > 0) && isNode1_1 c -> EqRk c t
      Exception is the singleton-case: (rk == 0) && isNode1_1 c => RkDiff t c 1   
  
  from that we conclude the following clauses for 1,1 / 2,2 (refining for t): 
    (isNode2_2 t || isNode1_1 t) ==> (RkDiff t s 0) <=> 
    not (isNode2_2 t || isNode1_1 t) || (RkDiff t s 0) <=> 
    (not (isNode2_2 t) && not (isNode1_1 t)) || (RkDiff t s 0) 

    then we can say for t in insert:
     (isNode1_1 t && rk t == 0) ==> RkDiff t s 1           <=> (not (isNode1_1 t && rk t == 0)) || RkDiff t s 1
     (isNode1_1 t && rk t > 0)  ==> RkDiff t s 0           <=> (not (isNode1_1 t && rk t > 0))  || RkDiff t s 0

  And finally, I added IsWavlNode t which made it valid. The same was done to balL/R
  -> my reasoning: by bounding the case group explicitly by defining all possible cases LH is able to determine which cases are allowed and which aren't

  refinement for potential annotation clauses: 
  (RkDiff s t 1) ==> (potT (tval t') + tcost t' <= potT s)     <=> 
   not (RkDiff s t 1) || (potT (tval t') + tcost t' <= potT s) <=> 
    ((EqRk t s) || (potT (tval t') + tcost t' <= potT s)) 

  and 
  (EqRk t s) ==> (potT (tval t') + tcost t' <= potT s + 3)     <=> 
   not (EqRk t s) || (potT (tval t') + tcost t' <= potT s + 3) <=> 
   (RkDiff s t 1) || (potT (tval t') + tcost t' <= potT s + 3)

  what we know / can exclude:
  * we don't need to specify both potT and potT2 bc we know that the input and output of insert is a wavl tree, thus satisfying potT, which has the stronger constraint, i.e. compare balL/R 

clause `isNode2_2nNil t ==> EqRk t s`:
  we know that `(not (isNode2_2 s) || (EqRk t s))`should also hold for insert, since if s is a 2,2-Node then regardless of the outcome of insert in a child the rk will stay
  the same. But here we have the problem that isNode2_2 does not allow Nil values so we had to add the helper inline function isNode2_2nNil, the small standing for 'not' 

to be inserted: 
  && (not (RkDiff s (tval t') 1) || (potT2 (tval t') + tcost t' <= potT2 s))
                          && (not (EqRk (tval t') s)     || (potT2 (tval t') + tcost t' <= potT2 s + 2))
  
--}
-- {-@ insert :: (Ord a) => a -> s:Wavl -> t':{Tick ({t:NEWavl | (EqRk t s || RkDiff t s 1) 
--           && (not (isNode2_2 t) || (EqRk t s)) 
--           && ((not (isNode1_1 t && rk t > 0)) || EqRk t s) && IsWavlNode t }) 
-- --           | tcost t' >= 0   
--              && (not (RkDiff s (tval t') 1) || amortized t' s)
--              && (not (EqRk (tval t') s)     || amortized1 t' s)
--                 }  @-} -- / [rk (tval t')]
```

## Extension: MT case for isNode2_2
The negated case set for a Wavl node which is a 2,2-node would be the all possible cases which are still Wavl but not 2,2: 1,1, 1,2 and 2,1. 
And we know that the negation of `eqRk t s` in our insert function for a given output is `rkDiff t s 1` bc the output can only ever be either equal rk or +1 in rank. Thus, we can form another constraint for our insert refinement (which we already defined for balL/R, incidentally): 
```haskell
(not (is0ChildN n r') || (isPromoteCase r'))
```
with
```haskell
isPromoteCase :: Tree a -> Bool
isPromoteCase t = (isNode1_1 t && rk t == 0) || isNode1_2 t || isNode2_1 t
```
