module Hello where

open import Data.Nat hiding (_*_)

data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello

halve : ℕ → ℕ
halve 0 = 0
halve (suc 0) = 0
halve (suc (suc n)) = suc (halve n)

_*_ : ℕ → ℕ → ℕ
_ * 0       = 0
x * (suc y) = x * y + x

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

_&&_ : Bool → Bool → Bool
false && _ = false
true && true = true
true && false = false

_||_ : Bool → Bool → Bool
false || false = false
false || true = true
true || _ = true
