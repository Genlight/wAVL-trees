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

{-@ type EqTes X H L R = {v:Tree a | ht1 v == H && left v == L && ht (right v) == ht (tval R) && left (right v) == left (tval R) } @-}

{-@ type EqCT T = {v:EqT T | rk T == rk v} @-}

{-@ type EqTeT X H L R = {v:Tick (v':EqTes X H L R) | ht1 (tval v) == H && left v == L && ht (right (tval v)) == ht (tval R) && left (right (tval v)) == left (tval R) } @-}
{-@ type EqTeTn X H L R = {v:EqTeT X H L R | not empty (tval v)} @-}
-- EqTs: we expect R :: Tick(Tree a)

{-@ type EqTs X H L R = {v:NETree | ht1 v == H && ht1 v == ht v && val v == X && left v == L && right v == tval R} @-}
{-@ type EqTsc X C H L R = {v:EqTs X H L R | rk v == C} @-}

{-@ type TTreeCol X C H L R = {v:Tick ({t:Tree | rk t == C && ht t == H && left t == L && right t == (tval R) }) | tcost v == tcost r } @-}
    --{v:EqTeTn X H L R | rk (tval v) == C  } @-} 

-- && right (tval v) == (tval R)
-- {-@ type EqTTs X H L R = {v:Tick (v':EqTs X H L R) | 
--                     ht1 (tval v) == H && left (tval v) == L && ht1 (tval v) == ht (tval v)
--                     && right (tval v) == tval R 
--                     && tcost R == tcost v } @-}
-- {-@ type EqTTsa X H L R = {v:EqTTs X H L R | potT (tval v) + tcost v <= potT T + 2} @-}

-- {-@ type  ... = {v:Tick ({t:EqTe }) | tcost R <= tcost v && tcost v <= tcost R + 2 potT (tval v) + tcost v <= potT T + 3} @-}
{-@ type EqTT T = Tick (v:EqT T) @-}

{-@ type EqTTa T = {v:EqTT T | potT (tval v) + tcost v <= potT T + 3} @-}
{-@ type EqCTT T = Tick (v:EqCT T) @-}

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
                    ((rk t == rk (tval v)) || (pot1 v + tcost v <= potT t)) } / [ht t] @-} -- EqTTa does not hold
testT :: Tree a -> Tick (Tree a)
testT t@(Tree x c h l Nil) 
    | c == B = RTick.wait (red t) -- t is leaf, amortised cost of 0
    | c == R = pure t -- t is leaf, no cost 
testT t@(Tree x c h l r) = checkT (rk r) x c h l r'
    where
        r' = testT r
        t' = treeR x c h l r'
        -- v = (ht r == ht (tval r')) ?= checkT (rk r) x c h l r'

-- {-@ help :: t:NETreeR -> v:EqTT a t / [ht t] @-}
-- help :: Tree a -> Tick (Tree a)
-- help t@(Tree x c h l r) = RTick.step (tcost (r')) (checkT (rk r) (Tree x c h l (tval (r'))))
--     where r' = testT r

--  | potT (tval v) + tcost v <= potT t + 2 
{-@ checkT :: Col -> x:a -> c:Col -> h:Pos -> l:ChildT a h -> r:Tick (r':ChildT a h) 
                    -> v:TT3 x h l r @-} -- EqTTa
checkT :: Col -> a -> Col -> Int -> Tree a -> Tick(Tree a) -> Tick( Tree a)
-- checkT _ Nil = pure Nil 
checkT z x c h l r
    | rk r' /= z && c == R   = RTick.step 2 t
    | rk r' /= z             = RTick.wmap red t
    | rk r' == z = t
        where 
            t = treeR x c h l r
            r' = tval r

-- {-@ checkT' :: Col -> t:Tick (t':Tree a) 
--                     -> {v:TT2 t | tcost v <= tcost t + 2 } @-}
-- checkT' :: Col -> Tick(Tree a) -> Tick(Tree a)
-- -- checkT _ Nil = pure Nil 
-- checkT' z t
--     | rk r /= z && c == R   = RTick.step 2 t
--     | rk r' /= z             = RTick.wmap red t
--     | rk r' == z = t
--         where 
--             r' = right (tval t)
--             c = col (tval t)
    
-- TRUSTED CODE, we assume that the costs are given from the child to the parent
{-@ treeR :: x:a -> c:Col -> h:Pos -> l:ChildT a h -> r:Tick (r':ChildT a h) -> {v:Tick ({t:NETree | left t == l && right t == tval r && ht t == h && rk t == c}) | tcost r == tcost v } @-} -- TTreeCol x c h l r
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

-- {-@ inline isBlack @-}
-- isBlack :: Tick (Tree a) -> Bool
-- isBlack t = rk (tval t) == B 

-- height :: Tree a -> Tree a -> Int
-- height l r = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

-- -- copied from my implementation in RTick, s. commit 
-- {-@ (<$>) :: f:(a -> b) -> t1:Tick a
--                     -> { t:Tick b | Tick (tcost t1) (f (tval t1)) == t }
-- @-}
-- infixl 4 <$>
-- (<$>) :: (a -> b) -> Tick a -> Tick b
-- (<$>) = RTick.fmap 
-- -- f <$> a <*> b <*> c = Tick (a1 + a2)

-- {-@ reflect liftM5 @-}
-- {-@ liftM5 :: g:(a -> b -> c -> d -> e -> f) -> t1:Tick a -> t2:Tick b -> t3:Tick c -> t4:Tick d -> t5:Tick e
--                     -> { t:Tick f | g (tval t1) (tval t2) (tval t3) (tval t4) (tval t5) == tval t &&
--                       tcost t1 + tcost t2 + tcost t3 + tcost t4 + tcost t5 == tcost t } @-}
-- liftM5 :: (a -> b -> c -> d -> e -> f) -> Tick a -> Tick b -> Tick c -> Tick d -> Tick e -> Tick f
-- liftM5 f (Tick m x) (Tick n y) (Tick n1 y1) (Tick n2 y2) (Tick n3 y3) = Tick (m + n + n1 + n2 + n3) (f x y y1 y2 y3)

