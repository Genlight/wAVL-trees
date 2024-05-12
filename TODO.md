# TODO's
* Beweis der **logarithmischen Höhe** 
* Beweis des **gesamten Aufwands**: rk t + pot t + 3 >= tcost (finding the node to delete) + tcost (balancing) + (remaining pot)
* Verbesserung von NIL case in delL **ODER** Aufzeigen, dass es nicht anders geht in LH -> Beweis!


# Arbeit schreiben

## erstes Kapitel 
sollte sein: 
* Motivation und Problem statement
kein konstantes Potential, 
Nicki amortisierte Comp. Analyse heraussuchen!!
* * invarianten Problem / wichtiges Design Prinzip
* * starke statische Invarianten haben, die forciert werden, die eine Herausforderung für die Verifzierung sind
Diese müssen in der Verifizierung immer wieder auf Richt. kontrolliert werden 
* State of the art / related Work
    siehe ATLAS / Isa/HOL
* Methodological approach
* Contributions

ATLAS kann weggelassen werden
## 2 Kap

über amort. Analyse

## 3. Kap

LH

## 4. Kap. 
rank-balanced Trees entweder mit 3 oder eigenes Kap


# Conclusion

Reflektion / Future work
Was noch gegangen wäre


# Code erklären

Ich muss zeigen, dass mein Approach zu POT, empty trees und den jeweiligen Refinements korrekt ist. 

weiters muss ich zeigen, dass die Umformung vom imperativen  Approach zu dem jetzigen legit ist. 


## Sonstiges
Mein Verständnis des Refinement Liftings kann ich vermtulich auch aufzeigen, i.e. es soll klar sein, dass weniger Funktionen teilweise besser sind, um etwas zu beweisen, da nach einem Beweis der Richtigkeit einer Funktion die Definition der Funktion aus dem constraint pool wegfällt. Dadurch gehen unter Umständen Informationen verloren, die man eigentlich gerne an einer abhängigen Stelle im code gerne hätte, da man sie implizit als Invariante erwartet.

Dem ist aber nicht so. 

invariant: balancedness in empty trees

