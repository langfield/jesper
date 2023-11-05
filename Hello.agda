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
_ * 0 = 0
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

id : (A : Set) → A → A
id A x = x

id' : {A : Set} → A → A
id' x = x

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A
infixr 5 _::_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

length : {A : Set} → List A → ℕ
length [] = 0
length (_ :: xs) = 1 + length xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : {A B : Set} → (A → B) → List A → List B
map _ [] = []
map f (x :: xs) = f x :: map f xs
