data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero    + y = y
(suc x) + y = suc (x + y)

not : Bool → Bool
not = {!!}

example : Nat
example = {! zero + zero !}
