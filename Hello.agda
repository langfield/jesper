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

-- Exercise 1.6.
-- Impossible to implement the nil case.
-- mystery : {A : Set} → List A → ℕ → A
-- mystery [] n = ?
-- mystery (x :: xs) n = x

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

[]→[]' : {A : Set} → List A → List' A
[]→[]' [] = []'
[]→[]' (x :: xs) = x ::' ([]→[]' xs)

[]'→[] : {A : Set} → List' A → List A
[]'→[] (zero , []ᵥ) = []
[]'→[] (suc n , x ::ᵥ xs) = x :: ([]'→[] (n , xs))

data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left x)  f _ = f x
cases (right x) _ g = g x

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where
  -- no constructors

absurd : {A : Set} → ⊥ → A
absurd ()

A→B→A : {A B : Set} → A → B → A
A→B→A a b = a

A∨⊤→A∨⊥ : {A : Set} → A × ⊤ → Either A ⊥
A∨⊤→A∨⊥ (a , _) = left a

A→B→C→A×B→C : {A B C : Set} → (A → B → C) → A × B → C
A→B→C→A×B→C f (a , b) = f a b

A×[B∨C]→[A×B]∨[A×C] : {A B C : Set} → A × (Either B C) → Either (A × B) (A × C)
A×[B∨C]→[A×B]∨[A×C] (x , left b) = left (x , b)
A×[B∨C]→[A×B]∨[A×C] (x , right c) = right (x , c)

[A→C]×[B→D]→A×B→C×D : {A B C D : Set} → (A → C) × (B → D) → A × B → C × D
[A→C]×[B→D]→A×B→C×D (f , g) (a , b) = f a , g b

-- We call `g`, which yields a value of type ⊥.
-- So we must have:
--  right (λ x → g (left x)) : Either P (P → ⊥)
--
-- And since this is a `right`, we must have:
--  λ x → g (left x) : P → ⊥
--
-- And since we already know the type of `g`, we must have that:
--  left x : Either P
--
-- And then:
--  x : P
--
-- Which makes sense, since the lambda function above has type: P → ⊥
f : {P : Set} → (Either P (P → ⊥) → ⊥) → ⊥
f g = g (right (λ x → g (left x)))

-- So the way to solve this problem is as follows:
--
-- 1. Read the type signature from right-to-left.
-- 2. We need a value of type ⊥.
-- 3. We can get a value of type ⊥ by calling g.
-- 4. Thus we need a value of type Either P (P → ⊥).
-- 5. We don't have a value of type P, so no luck there.
-- 6. So we must construct a value of type P → ⊥.
-- 7. So we have λ x = ? : P → ⊥.
-- 8. Now we have a value of type P! It is x.
-- 9. We were looking for that earlier, so now we can call g.
-- 10. So we call g on left x.
-- 11. And we get λ x = g (left x) : P → ⊥.
-- 12. Then we call g again on that and we're done.
