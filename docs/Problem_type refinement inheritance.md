# Problem Description

reusing functions from [WAVl.hs](src/WAVL.hs) in [PotentialAnalysis_WAVL.hs](src/PotentialAnalysis_WAVL.hs) led to some unexpected behaviour, e.g.
I expected that by importing a library like `WAVL`
in `PotentialAnalysis_WAVL` would lead to all used types also to be available (e.g. at least that was my original thought). After some testing and some incosistencies i can say for sure that: 

* Predicates are loaded and are available without the need for a qualified name (e.g. `Rkdiff`)
* Measures are also loaded and could be used, but needed in some places a qualified name (e.g. `WAVL.notEmptyTree`)
* data constructor and their respective sub functions (e.g. `rd` or `left`) I am confident to use without the qualifier
* Types, displayed different behaviour. To use them in `PotentialAnalysis_WAVL` I retyped all types but with the difference that I used qualified names for all 