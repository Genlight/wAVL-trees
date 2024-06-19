# Proving theorems about weak AVL trees

## functional correctness
We show via the LiquidHaskell framework that my functional Implementation of the wAVL trees are functional correct for insert and delete. 

## Potential Analysis for Complexity 
We prove automatically the theorems regarding the complexity of weak AVL trees first proven by hand in {Haeupler, 2015 #48}. 

# merged potential annotation for insert and delete
We redefined the used potential function in Haeupler et. al such that the previously separately proven potential is now combined: 
> "Das Potential von 2,2 und 2,3 nodes ist 2, das Potential von 1,1 und 0,1 nodes ist 1, das Potential von allen anderen nodes ist 0."

# Proof on the logarithmic Height of wAVL trees
We use axioms for our proofs for the Monotonicity of the natural Logarithm and the relation to the exponential at [./src/PotentialAnalysis_WAVL_v2.hs]. 

The axioms are originally defined in Hochrainer, J. (2024) in her work on Amortized Cost Analysis on Binomial Heaps. 

# References
Haeupler, B., et al. (2015). "Rank-Balanced Trees." ACM Transactions on Algorithms 11(4): 1-26.

Hochrainer, J. (2024). Formalizing an Amortized Cost Analysis of Binomial Heaps and Fibonacci Heaps in Liquid Haskell. Faculty of Mathematics, Computer Science and Physics. Innsbruck, University of Innsbruck. MSc.: 66.
	
