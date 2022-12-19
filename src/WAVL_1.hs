module WAVL_1 (Tree, singleton,
 insert,
  ht, bFac) where

-- Basic functions
{-@ data Tree [ht] @-} 
data Tree a = Nil | Tree a Int (Tree a) (Tree a) deriving Show

{-@ measure ht @-}
{-@ ht :: Tree a -> Nat @-}
ht              :: Tree a -> Int
ht Nil          = 0
ht (Tree x n l r) = if (ht l) > (ht r) then (1 + ht l) else (1 + ht r)

{-@ measure bFac @-}
bFac Nil          = 0
bFac (Tree v n l r) = ht l - ht r

{-@ htDiff :: s:Tree a -> t: Tree a -> {v: Int | HtDiff s t v} @-}
htDiff :: Tree a -> Tree a -> Int
htDiff l r = ht l - ht r

{-@ emp :: {v: Wavl | ht v == 0 && rk v == (-1) } @-}
emp = Nil

{-@ singleton :: a -> {v: Wavl | rk v == 0 && ht v == 1 && notEmptyTree v} @-}
singleton a = Tree a 0 Nil Nil

{-@ measure notEmptyTree @-}
notEmptyTree :: Tree a -> Bool
notEmptyTree Nil = False
notEmptyTree _ = True

-- | Insert functions
insert :: (Ord a) => a -> Tree a -> Tree a
insert x Nil = singleton x
insert x t@(Tree v n l r) = case compare x v of
    LT -> insL
    GT -> insR
    EQ -> t
    where r' = insert x r
          l' = insert x l
          lt' = Tree v n l' r
          rt' = Tree v n l r'
          insL | rk l' < n = lt'
               | rk l' == rk r + 1 = promote lt'
               | (rk (left l') + 1) == rk l' = rotateRight lt' 
               | otherwise = rotateDoubleRight lt' 
          insR | rk r' < n = rt'
               | rk r' == rk l + 1 = promote rt'
               | rk (right r') +1 == rk r' = rotateLeft rt'
               | otherwise = rotateDoubleLeft rt'

promote :: Tree a -> Tree a
promote (Tree a n l r) = (Tree a (n+1) l r)

rotateRight :: Tree a -> Tree a
rotateRight (Tree x n (Tree y m a b) c) = Tree y m a (Tree x (n-1) b c)
rotateRight _ = error "not matched Tree structure"

rotateDoubleLeft :: Tree a -> Tree a
rotateDoubleLeft t@(Tree x n a (Tree y m (Tree z o b_1 b_2) c)) =
  Tree z (o+1) (Tree x (n-1) a b_1) (Tree y (m-1) b_2 c) 
rotateDoubleLeft _ = error "not matched Tree structure"

rotateLeft :: Tree a -> Tree a
rotateLeft t@(Tree x n a (Tree y m b c)) = Tree y m (Tree x (n-1) a b) c
rotateLeft _ = error "not matched Tree structure"

rotateDoubleRight :: Tree a -> Tree a
rotateDoubleRight t@(Tree x n (Tree y m a (Tree z o b_1 b_2)) c) = 
  Tree z (o+1) (Tree y (m-1) a b_1) (Tree  x (n-1) b_2 c) 
rotateDoubleRight _ = error "not matched Tree structure"

-- Test
main = do
    mapM_ print [a,b,c,d]
  where
    a = singleton 5
    b = insert 2 a
    c = insert 3 b
    d = insert 7 c

-- Liquid Haskell
{-@ predicate HtDiff S T D = (ht S) - (ht T) == D @-}
{-@ predicate EqHt S T = (ht S) == (ht T) @-}

-- predicates by me
{-@ predicate EqRk S T = rk T == rk S @-}
{-@ predicate RkDiff S T D = (rk S) - (rk T) == D @-}

{-@ measure balanced @-}
balanced :: Tree a -> Bool
balanced Nil = True
balanced t@(Tree _ n l r) = rk r < n && n <= rk r + 2
                       && rk l < n && n <= rk l + 2
                       && (balanced l)
                       && (balanced r)

-- my additions
{-@ type Rank = {v:Int | v >= -1 } @-}
{-@ type AlmostWavl = {t:Tree | not (notEmptyTree t) || ((balanced (left t) && balanced (right t))) } @-}

{-@ measure left @-}
{-@ left :: {t:Tree a | notEmptyTree t } -> Tree a @-}
left :: Tree a -> Tree a
left (Tree _ _ l _) = l

{-@ measure right @-}
{-@ right :: {t:Tree a | notEmptyTree t } -> Tree a @-}
right :: Tree a -> Tree a
right (Tree _ _ _ r) = r

{-@ measure rk @-}
-- {-@ rk :: Tree a -> Rank @-}
rk :: Tree a -> Int
rk Nil =  -1
rk (Tree _ n _ _) = n

{-@ type Wavl = {v: Tree a | balanced v} @-}
