{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module LogPow ( log2
              , pow2
              , log2_mon
              , pow2_mon
              , log2_pow2
              ) where

{-@
reflect log2
log2 :: {i:Int | i >= 1} -> {r:Nat | r < i}
@-}
log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 (div n 2)

{-@ log2_mon :: {a:Int | a >= 1} -> {b:Int | a <= b} -> {log2 a <= log2 b} @-}
log2_mon :: Int -> Int -> ()
log2_mon 1 x = const () (log2 x >= 0)
log2_mon _ 1 = ()
log2_mon x y = log2_mon (div x 2) (div y 2)

{-@ log2_pow2 :: n:Nat -> {log2 (pow2 n) = n} @-}
log2_pow2 :: Int -> ()
log2_pow2 0 = ()
log2_pow2 n = log2_pow2 (n-1)

{-@
reflect pow2
pow2 :: Nat -> {r:Int | r >= 1}
@-}
pow2 :: Int -> Int
pow2 0 = 1
pow2 n = 2 * pow2 (n-1)

{-@ pow2_mon :: a:Nat -> {b:Nat | a >= b} -> { pow2 a >= pow2 b } @-}
pow2_mon :: Int -> Int -> ()
pow2_mon 0 _ = ()
pow2_mon n 0 = pow2_mon (n-1) 0
pow2_mon n k = pow2_mon (n-1) (k-1)