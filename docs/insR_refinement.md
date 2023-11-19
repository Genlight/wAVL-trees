# Versuch: insR aus insert rausnehmen und stärkere Constraints erstellen

## 1. Versuch: 1-zu-1 wie im insert, nur ohne compare case

```haskell
{-@ insR :: (Ord a) => x:a -> {s:Wavl | val s < x } -> t:EqT s @-}
insR :: (Ord a) => a -> Tree a -> Tick (Tree a)
insR x t@(Tree v n l r)
  | rk (tval r') < n                       = treeRW1 v n l r' 
  | is0ChildN n r'' && rk r'' == rk l + 1  = RTick.wmap promoteR (treeR v n l r')
  | is0ChildN n r''                        = RTick.fmap balR (treeR v n l r')
    where
      r' = insert x r
      r'' = tval r' 
```

Problem mit diesem Ansatz war, dass wir einen Pattern-matching-non-exhaustive-Error bekommen haben. Ohne die linke Seite des Algorithmus kann diese nicht bewiesen werden. 

Der Ansatz wäre hier wieder, ein stärkeres refinement des inputs zu erstellen, um den Output weiter einzuschränken. Das führt idR dazu, dass LH erkennt, dass es keine weiteren Möglichkeiten gibt, wie das Pattern gematched werden kann. Das führt dann zu einem safe vom Compiler und ein otherwise case kann weggelassen werden. 

Dies ist wiederum erstrebenswert, da der otherwise-case in LH zu fehlern führen kann bzw. nicht leicht bewiesen werden kann. 

Eine einfache Erklärung dazu liegt vor: 
Eine if-Klausel kann in die Logik mit einer Implikation übernommen werden. Die Else-Klausel umfasst dabei alle "restlichen" Cases, die darin nicht reinfallen. 
Hier wird es aber bereits schwierig zu erkennen, dass dies keine simple Verneinung der Vorbedingung ist. Der Programmierer muss sich an dieser Stelle über sein Modell und alle Zustände, die dieses annehmen kann, sicher sein. 

Wie kann der Programmierer diese erkennen?
Für unser konkretes Beispiel betrachten wir die Menge an möglichen Zuständen von Wavl-Bäumen: 
In unserem Beispiel interessiert uns nur der Rank-Unterschied zwischen dem Node selbst und seinen direkten Kindern. 
In einem WAVL-Baum kann der Node 1,1, 2,2, 1,2 und 2,1 sein. LH erkennt nun in unserem Beispiel, dass wenn der erste case nicht hält (also `rk (tval r') < n` zu False evaluiert), dann können die restlichen zwei Cases theoretisch nicht alle Cases abfangen, die von einem `insert x r` zurückgegeben werden. Dies ist dem Return-Wert von `insert` geschuldet, welches ein offeneres Refinement hat, da dieses ja auch mehr Fälle auffangen muss. 

## Fazit
Unser Beispiel kann damit so nicht umgesetzt werden. Um stärkere Constraints auf die Funktion anzuwenden, wird eine andere Unterteilung benötigt. 

## 2. Versuch: insR nur mehr mit dem Rückgabewert von insert
Der Versuch fußt auf der Annahme, dass wir das oben aufgezeigte Beispiel nicht ohne einen otherwise case zum Laufen bringen können und dass wir aufgrund der otherwise-Problematik in LH diese soweit es geht nicht in unserer Problemformulierung verwenden wollen.

## Problem: fmap Rückgabewert ist nicht Wavlnode
Wir benötigen die Constraints von balR, im speziellen wird das output refinement von balR nicht akzeptiert: 
```haskell
-- zu beweisen: {t:EqT s | amortisedStmt s t }
{-@ insR ::  x:a  -> n:NodeRank -> l:ChildB n -> r:Tick ({r':ChildW n | notEmptyTree r' && n <= (rk r') + 2}) 
          -> t:Tick (t':EqDiffWavl n) @-}
insR :: a -> Int -> Tree a -> Tick(Tree a) -> Tick(Tree a)
insR v n l r
  | rk (tval r) < n                      = treeRW1 v n l r 
  | is0ChildN n r' && rk r' == rk l + 1  = RTick.wmap promoteR (treeR v n l r)
  | is0ChildN n r'                       = assert (isWavlNode (tval (RTick.fmap balR (treeR v n l r)))) ?? RTick.fmap balR (treeR v n l r)
    where
      r' = tval r
```

mit balR: 
```haskell
{-@ balR :: {v:Node2_0 | ((isNode1_1 (right v) && rk (right v) == 0) || isNode2_1 (right v) || isNode1_2 (right v)) }
          -> {t:EqRkWavl v | (potT t <= potT2 v + 2)}  @-} -- amortisiert == 2
balR :: Tree a -> Tree a
balR t@(Tree x n l r)  
  | (rk (left r) + 2) == rk r = rotateLeft t 
  | (rk (left r) + 1) == rk r = rotateDoubleLeft t
```

und den types: 
```haskell
{-@ type EqRkWavl v = {t:NEWavl | EqRk v t && isWavlNode t } @-}

```

ergibt die FM: 
```haskell
is not a subtype of the required type
  VV : {VV : (PotentialAnalysis_WAVL.Tree a) | (rk (right VV) == 0
                                                && rk (left (right VV)) + 1 == rk (right VV)
                                                && rk (right (right VV)) + 1 == rk (right VV))
                                               || ((notEmptyTree (right (right VV))
                                                    && rk (left (right VV)) + 2 == rk (right VV)
                                                    && rk (right (right VV)) + 1 == rk (right VV))
                                                   || (notEmptyTree (left (right VV))
                                                       && rk (left (right VV)) + 1 == rk (right VV)
                                                       && rk (right (right VV)) + 2 == rk (right 
```
Was bedeutet, dass LH nicht erkennt, dass `RTick.fmap balR (treeR v n l r)` das refinement `ìsWavlNode t` auf dem Rückgabewert hat. Da `balR` dies sehr wohl auf seinem Rückgabewert hat, scheint es hier zum Verlust des besagten refinement bzw. zu einem Erasure zu kommen. Dies passiert sehr wahrscheinlich bei der Neuerstellung des Monad-gewrappten Typen und Rückgabewert von `fmap`. Da es sich bei einem gewrappten Monaden immer um ein neues Objekt handelt, gehen hier nicht weitergegebene Constraints verloren. Es werden für die Berechnung des Rückgabewerts nur der Output von `fmap` verwendet.  

## Versuch 3: isPromoteCase 
Ein weiterer Versuch, war den isPromoteCase explizit zu propagieren: 
```haskell
{-@ inline isPromoteCase @-}
isPromoteCase :: Tree a -> Bool
isPromoteCase t = (isNode1_1 t && rk t == 0) || isNode1_2 t || isNode2_1 t
```

im insert refinement mittels implikation: 
```haskell
... && (not (is0ChildN n r') || (isPromoteCase r')) ...
```