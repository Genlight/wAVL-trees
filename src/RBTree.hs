{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--bscope" @-}

{- 
    simple tree function which colours each node either Red or Black
    for our potential analysis we say that each black node has potential of 1 and each red node potential of 0
    
    test function: 
        1. go down the right path, i.e. selecting always the right child node
        2. if the last node (leaf) is Black switch it to red, else leave it unchanged

    this test function shall showcase a simplified function of the more complex wavl-insert case

    check function: 
        symbolises our "stop" case analog to a rotate case in a wavl tree
        this step showcases our problem to prove that this stop case only happens exactly once during the rebuilding of the tree

    checkT:     
        check function + using RTick Monad
        we want to show that this case incurs a cost of 2 (nothing special about that) but does not change the potential
        By this choice we want to show that the potential is changed at each step by -1 until the stop case. Further we incur cost +1 at each step
        resulting in an amortised cost at each step (not including the stop case) of 0. 

    testT: 
        test function + using RTick Monad
        We want to show that there is only one stop case, thus in total we incur an amortized cost of 2 (stop case + all other cases).

        to prove (as a function refinement): 
            potT (tval v) + tcost v <= potT (tval t) + tcost t + 2
        
------------------------------

    Deutsch - German
    
    Die test Funktion steigt nun immer in das rechte Kind ab. Dann bauen
    wir den Baum wieder rekursiv zusammen wie in wavl-insert. Wenn wir
    ein Blatt erreichen ändern wir die Farbe von schwarz auf rot, das hat
    Kosten 1. Wenn die Farbe rot ist, machen wir nichts. Beim aufsteigen
    checken wir immer, ob sich die Farbe des Teilbaums beim rekursiven
    Aufruf geändert hat. Wenn sie sich geändert hat, machen wir das selbe
    wie beim Blatt Fall. Wenn sie sich nicht geändert hat machen wir nichts.
-}

module RBTree where 

import Prelude hiding (pure, (<*>), (>>=), (<$>), liftM2)
import Language.Haskell.Liquid.RTick as RTick

data Col = R | B deriving (Eq, Show)

{-@ data Tree [ht1] a = Nil | Tree { val :: a, 
                                    rd :: Col,
                                    ht1 :: v:Pos,
                                    left :: ChildT a ht1,
                                    right :: ChildT a ht1 } @-} 
data Tree a = Nil | Tree { val :: a, rd :: Col, ht1:: Int, left :: (Tree a), right :: (Tree a)} deriving Show


{-@ type ChildT a T = {v:Tree a | ht v + 1 <= T } @-}
{-@ type Nat = {v:Int | v >= 0} @-}
{-@ type Pos = {v:Int | v >= 1} @-}
{-@ type NETree = {v:Tree a | not empty v} @-}
{-@ type NETreeR = {t:NETree | not empty (right t)} @-}
{-@ type EqT T = {v:EqTe T | not empty v } @-}
{-@ type EqTe T = {v:Tree a | ht1 v == ht1 T && left v == left T && ht (right v) == ht (right T) && left (right v) == left (right T) && ht T == ht v} @-}

{-@ type TT1 T = v:Tick ({v':NETree | left v' == left T && ht v' == ht T}) @-}
{-@ type TT2 T = {v:Tick ({v':NETree | left v' == left (tval T) && ht v' == ht (tval T)}) | left (tval v) == left (tval T)} @-}
{-@ type TT3 X H L R = {v:Tick ({t:NETree | ht t == H && left t == L && ht (right t) == ht (tval R) }) | tcost v <= tcost r + 2 } @-}
{-@ type TT4 X H L R = {v:TT3 X H L R | pot1 v + tcost v <= potT L + pot1 R + 1 + 2 } @-}

{-@ measure potT @-}
{-@ potT :: t:Tree a -> Nat / [ht t] @-}
potT :: Tree a -> Int
potT Nil = 0
potT t@(Tree _ c _ l r) 
    | c == B = 1 + potT l + potT r
    | otherwise = potT l + potT r

{-@ inline pot1 @-}
{-@ pot1 :: v:Tick (Tree a) -> Nat @-}
pot1 :: Tick (Tree a) -> Int
pot1 t = potT (tval t)


{-@ measure ht @-}
{-@ ht :: t:Tree a -> {v:Nat | v >= 0 && (empty t || (v >= ht (left t) + 1 && v >= ht (right t) + 1))} @-}
ht              :: Tree a -> Int
ht Nil          = 0
ht (Tree x n h l r) = h -- if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

{-@ measure empty @-}
empty :: Tree a -> Bool
empty Nil = True
empty t@(Tree _ _ _ _ _) = False 

{-@ measure rk @-}
rk :: Tree a -> Col
rk Nil = R
rk t@(Tree _ c _ _ _) = c

{-@ test :: t:Tree a -> v:EqTe t @-}
test :: Tree a -> Tree a
test Nil = Nil
test t@(Tree x c h l r) 
    | empty r && c == B = red t -- t is leaf, cost of 1 is incurred, and pot - 1
    | empty r && c == R = Tree x c h l r -- t is leaf, no cost 
    | otherwise = undefined -- check (rk r) (Tree x c h l (test r)) -- do the checking which changes colours to red if a change happened in r

{-@ check :: Col -> t:NETree -> v:EqT t @-}
check :: Col -> Tree a -> Tree a
check c t@(Tree a b h l r) 
    | rk r == c = t -- no change
    | rk r /= c && b == R = t -- this is the "rebalancing" step we are looking for, set cost to 2, no pot change
    | otherwise = red t  -- change B to R, incur cost of 1 and pot - 1

-- do the checking which changes colours to red if a change happened in r
{-@ testT :: t:NETree -> {v:TT1 t | 
                    ((rk t /= rk (tval v)) || (pot1 v + tcost v <= potT t + 2)) || 
                    ((rk t == rk (tval v)) || (pot1 v + tcost v <= potT t)) } / [ht t] @-}
testT :: Tree a -> Tick (Tree a)
testT t@(Tree x c h l Nil) 
    | c == B = RTick.wait (red t) -- t is leaf, amortised cost of 0
    | c == R = pure t -- t is leaf, no cost 
testT t@(Tree x c h l r) = checkT (rk r) x c h l r'
    where
        r' = testT r
        t' = treeR x c h l r'

{-@ checkT :: Col -> x:a -> c:Col -> h:Pos -> l:ChildT a h -> r:Tick (r':ChildT a h) 
                    -> v:TT3 x h l r @-} 
checkT :: Col -> a -> Col -> Int -> Tree a -> Tick(Tree a) -> Tick( Tree a)
-- checkT _ Nil = pure Nil 
checkT z x c h l r
    | rk r' /= z && c == R   = RTick.step 2 t
    | rk r' /= z             = RTick.wmap red t
    | rk r' == z = t
        where 
            t  = treeR x c h l r
            r' = tval r
   
-- TRUSTED CODE, we assume that the costs are given from the child to the parent
{-@ treeR :: x:a -> c:Col -> h:Pos -> l:ChildT a h -> r:Tick (r':ChildT a h) -> {v:Tick ({t:NETree | left t == l && right t == tval r && ht t == h && rk t == c}) | tcost r == tcost v } @-}
treeR :: a -> Col -> Int -> Tree a -> Tick(Tree a) -> Tick(Tree a)
treeR x c h l r = Tick (tcost r) (Tree x c h l (tval r))

{-@ red :: {t:NETree | rk t == B } -> {v:EqT t | potT t == potT v + 1 } @-}
red :: Tree a -> Tree a
red t@(Tree a _ h l r) = Tree a R h l r

{-@ reflect ?? @-}
{-@ (??) :: a -> y:b -> {v:b | v == y } @-}
(??) :: a -> b -> b
x ?? y = y

{-@ reflect ?= @-}
{-@ (?=) :: {y:Bool | y == True } -> z:a -> {v:a | z == v} @-}
(?=) :: Bool -> a -> a
y ?= x = x
