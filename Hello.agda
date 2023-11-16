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

_++ᵥ_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[]ᵥ ++ᵥ ys = ys
(x ::ᵥ xs) ++ᵥ ys = x ::ᵥ (xs ++ᵥ ys)

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

lookupᵥ : {n : ℕ}{A : Set} → Vec A n → Fin n → A
lookupᵥ (x ::ᵥ xs) zero = x
lookupᵥ (x ::ᵥ xs) (suc i) = lookupᵥ xs i

putᵥ : {A : Set}{n : ℕ} → Fin n → A → Vec A n → Vec A n
putᵥ zero x' (x ::ᵥ xs) = (x' ::ᵥ xs)
putᵥ (suc i) x' (x ::ᵥ xs) = x ::ᵥ (putᵥ i x' xs)

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

_×'_ : (A B : Set) → Set
A ×' B = Σ A (λ _ → B)

×'→× : {A B : Set} → A ×' B → A × B
×'→× (x , y) = x , y

×→×' : {A B : Set} → A × B → A ×' B
×→×' (x , y) = x , y

List' : (A : Set) → Set
List' A = Σ ℕ (Vec A)

[]' : {A : Set} → List' A
[]' = 0 , []ᵥ

_::'_ : {A : Set} → A → List' A → List' A
x ::' (n , xs) = suc n , x ::ᵥ xs
