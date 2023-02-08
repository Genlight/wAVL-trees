# Problem description

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