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
