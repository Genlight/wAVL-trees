# Problem description (partially solved)

I try to construct a tree recursively and I have Ticks (costs) generated at the leafs of my tree. Now, when I reconstruct / travel the tree upwards I need to return the Ticks from the child node to the parent node. 

## Project lhTest

s. https://github.com/Genlight/lhTest 

I am using the data type
```haskell
-- Basic functions
{-@ data Tree [rk] a = Nil | Tree { val :: a, 
                                    rd :: {v:Int | v >= 0 }, 
                                    left :: Tree a,
                                    right :: Tree a } @-} 
data Tree a = Nil | Tree { val :: a, rd :: Int, left :: (Tree a), right :: (Tree a)} deriving Show

```

and try to analyse it in a separate file [PotentialAnalysis_WAVL.hs](src/PotentialAnalysis_WAVL.hs).

## concrete problem

In my recursive function call `delete` the tree structure is rebuild bottom-up. So essentially, after deleting a single node, by using recursively

```haskell
balDel (Tree (...))
```
I balance the tree structure according to the WAVL spec. The problem i face is that I get a Tick monad `Tick (Tree a)`

returned from the recursive `delete` call and want to use it as a child tree in the next step. so in order to reuse most of the code from [WAVL.hs](src/WAVL.hs) I do this in line 121 of [PotentialAnalysis_WAVL](src/PotentialAnalysis_WAVL.hs):

```haskell
t =  (pure Tree) `ap` (pure x) `ap` (pure n) `ap` (pure l) `ap` r
```

In essence, i have one child node `l` which has no Tick Monad and one `r` which has one. I want to combine all accumulated Ticks and return a new Tree which can then be rebalanced in some form.

With this, I get the following error message:

```bash
[2 of 2] Compiling PotentialAnalysis_WAVL

**** LIQUID: ERROR *************************************************************

<no location info>: error:
    /home/master/lhTest:1:1-1:1: Error
  crash: SMTLIB2 respSat = Error "line 6971 column 108: Wrong number of arguments (0) passed to function (declare-fun WAVL.Tree             (Int Int (WAVL.Tree Int) (WAVL.Tree Int))             (WAVL.Tree Int))"



--  While building package lhTest-0.1.0.0 (scroll up to its section to see the error) using:
      /home/master/.stack/setup-exe-cache/x86_64-linux/Cabal-simple_mPHDZzAJ_3.2.1.0_ghc-8.10.7 --verbose=1 --builddir=.stack-work/dist/x86_64-linux/Cabal-3.2.1.0 build lib:lhTest --ghc-options " -fdiagnostics-color=always"
    Process exited with code: ExitFailure 1
```

I tried my luck with the applicative functor `<*>` but that one could not be used with multiple arguments, only with two. 

I also thought about using a Tick equivalent to `liftM4` but I found that it wasn't specified in the RTick library yet. 

## new Trial & Error, Part 2
After emailing with NikiVarouz I tried to make a simpler Code problem, to minimally point my finger on the problem.

What I found, when I only try to add the tick type to it like in [test_RTick.hs](src/test_RTick.hs) it works as expected. 

test_RTick is basically only one function: 
```haskell
tickWrapper :: a -> Int -> Tree a -> Tick (Tree a) -> Tick (Tree a)
tickWrapper x n l r = (pure Tree) `ap` (pure x) `ap` (pure n) `ap` (pure l) `ap` r
``` 

But when I tried to import the `Tree` data type via `import WAVL` it failed with the unspecified SMTLIB2 error, as above.

Next try was to add the `tickWrapper` function directly to the [WAVL.hs](src/WAVL.hs) file and I got a new error: 

```bash
[1 of 1] Compiling WAVL             ( src/WAVL.hs, interpreted )

**** LIQUID: ERROR *************************************************************

<no location info>: error:
    :1:1-1:1: Error
  elaborate solver elabBE 3119 "VV##F##53" {VV##F##53 : func(0 , [(GHC.Prim.State# GHC.Prim.RealWorld);
                       (Tuple (GHC.Types.TupleRep (GHC.Types.$91$$93$ GHC.Types.RuntimeRep)) GHC.Types.LiftedRep (GHC.Prim.State# GHC.Prim.RealWorld) Tuple)]) | [(VV##F##53 =
                                                                                                                                                                     (Data.Foldable.mapM_ lq_anf$##7205759403792897895##dr8b lq_anf$##7205759403792897903##dr8j))]} failed on:
      VV##F##53 == Data.Foldable.mapM_ lq_anf$##7205759403792897895##dr8b lq_anf$##7205759403792897903##dr8j
  with error
      Cannot unify (@(6823494) @(6823496)) with func(0 , [(GHC.Prim.State# GHC.Prim.RealWorld);
          (Tuple (GHC.Types.TupleRep (GHC.Types.$91$$93$ GHC.Types.RuntimeRep)) GHC.Types.LiftedRep (GHC.Prim.State# GHC.Prim.RealWorld) Tuple)]) in expression: Data.Foldable.mapM_ lq_anf$##7205759403792897895##dr8b 
  in environment
      Data.Foldable.mapM_ := func(4 , [func(0 , [@(2); (@(1) @(3))]);
                                       (@(0) @(2));
                                       (@(1) Tuple)])

      VV##F##53 := func(0 , [(GHC.Prim.State# GHC.Prim.RealWorld);
                             (Tuple (GHC.Types.TupleRep (GHC.Types.$91$$93$ GHC.Types.RuntimeRep)) GHC.Types.LiftedRep (GHC.Prim.State# GHC.Prim.RealWorld) Tuple)])

      lq_anf$##7205759403792897895##dr8b := func(0 , [(WAVL.Tree int);
                                                      (GHC.Prim.State# GHC.Prim.RealWorld);
                                                      (Tuple (GHC.Types.TupleRep (GHC.Types.$91$$93$ GHC.Types.RuntimeRep)) GHC.Types.LiftedRep (GHC.Prim.State# GHC.Prim.RealWorld) Tuple)])

      lq_anf$##7205759403792897903##dr8j := [(WAVL.Tree int)]
```

## Environment

Ubuntu (in WSL2):
```bash
$ lsb_release -a
No LSB modules are available.
Distributor ID: Ubuntu
Description:    Ubuntu 20.04.3 LTS
Release:        20.04
Codename:       focal
```

Z3:
```bash
master@Dell:~/lhTest$ z3 --version
Z3 version 4.8.7 - 64 bit
master@Dell:~/lhTest$ stack exec z3 -- --version
Z3 version 4.8.7 - 64 bit
```

LiquidHaskell als GHC Plugin: 
```bash
master@Dell:~/lhTest$ stack exec liquid -- --version
LiquidHaskell Version 0.8.10.7.1 no git information
Copyright 2013-19 Regents of the University of California. All Rights Reserved.
```

Stack: 
```bash
master@Dell:~/lhTest$ stack --version
Version 2.9.1, Git revision 409d56031b4240221d656db09b2ba476fe6bb5b1 x86_64 hpack-0.35.0
```

GHC: 
```bash
master@Dell:~/lhTest$ stack exec ghc -- --version
The Glorious Glasgow Haskell Compilation System, version 8.10.7
```

GHCup: 
```bash
master@Dell:~/lhTest$ ghcup --version
The GHCup Haskell installer, version v0.1.18.0
```

# Test with the online editor (in-browser)
http://goto.ucsd.edu:8090/index.html#?demo=permalink%2F1675851706_19795.hs

## (hack-ish) Solution 
using a function as a wrapper for the data constructor seems to undo the smtlib2 error:

```haskell
{-@ tree :: x:a -> n:NodeRank -> l:Wavl' -> r:Wavl' -> {t:NEAlmostWavl' | WAVL.rk t == n && WAVL.left t == l && WAVL.right t == r && WAVL.val t == x} @-}
tree :: a -> Int -> Tree a -> Tree a -> Tree a
tree x n l r = Tree x n l r 
```