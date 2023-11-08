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

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

lookup : {A : Set} → List A → ℕ → Maybe A
lookup [] _ = nothing
lookup (x :: xs) 0 = just x
lookup (x :: xs) (suc i) = lookup xs i

data Vec (A : Set) : ℕ → Set where
  []ᵥ : Vec A 0
  _::ᵥ_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
infixr 5 _::ᵥ_

downFrom : (n : ℕ) → Vec ℕ n
downFrom 0 = []ᵥ
downFrom (suc k) = k ::ᵥ downFrom k

head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ::ᵥ xs) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail (x ::ᵥ xs) = xs

-- | Dot product.
_∙_ : {n : ℕ} → Vec ℕ n → Vec ℕ n → ℕ
(x ::ᵥ xs) ∙ (y ::ᵥ ys) = x * y + xs ∙ ys
[]ᵥ ∙ _ = 0
