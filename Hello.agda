module Hello where

open import Data.Bool
open import Data.Nat hiding (_*_)

data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello

halve : ℕ → ℕ
halve zero = zero
halve (suc zero) = zero
halve (suc (suc n)) = suc (halve n)

_*_ : ℕ → ℕ → ℕ
0 * _ = 0
_ * 0 = 0
(suc x) * y = x * y + y
