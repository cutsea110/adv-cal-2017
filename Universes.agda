module Universes where

data False : Set where
record True : Set where

data Bool : Set where
  true : Bool
  false : Bool

isTrue : Bool → Set
isTrue true = True
isTrue false = False

infix 30 not_
infixr 2 _and_

not_ : Bool → Bool
not true = false
not false = true

_and_ : Bool → Bool → Bool
true and x = x
false and _ = false

notNotId : (a : Bool) → isTrue (not not a) → isTrue a
notNotId true p = p
notNotId false ()

andIntro : (a b : Bool) → isTrue a → isTrue b → isTrue (a and b)
andIntro true y p₁ p₂ = p₂
andIntro false y () p₂

open import Data.Nat

nonZero : ℕ → Bool
nonZero zero = false
nonZero (suc n) = true

postulate _div_ : ℕ → (m : ℕ){p : isTrue (nonZero m)} → ℕ

three = 16 div 5

-----

data Functor : Set₁ where
  |Id|  : Functor
  |K|   : Set → Functor
  _|+|_ : Functor → Functor → Functor
  _|x|_ : Functor → Functor → Functor

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

data _⊛_ (A B : Set) : Set where
  _,_ : A → B → A ⊛ B

infixr 50 _|+|_ _⊕_
infixr 60 _|x|_ _⊛_

[_] : Functor → Set → Set
[ |Id| ] X = X
[ |K| A ] X = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |x| G ] X = [ F ] X ⊛ [ G ] X

map : (F : Functor){X Y : Set} → (X → Y) → [ F ] X → [ F ] Y
map |Id| f x = f x
map (|K| A) f c = c
map (F |+| G) f (inl x) = inl (map F f x)
map (F |+| G) f (inr x) = inr (map G f x)
map (F |x| G) f (x , y) = map F f x , map G f y

data μ_ (F : Functor) : Set where
  In : [ F ] (μ F) → μ F

out : {F : Functor} → μ F → [ F ] (μ F)
out (In x) = x

mapFold : ∀ {X} F G → ([ G ] X → X) → [ F ] (μ G) → [ F ] X
mapFold |Id| G φ (In x) = φ (mapFold G G φ x)
mapFold (|K| A) G φ c = c
mapFold (F₁ |+| F₂) G φ (inl x) = inl (mapFold F₁ G φ x)
mapFold (F₁ |+| F₂) G φ (inr x) = inr (mapFold F₂ G φ x)
mapFold (F₁ |x| F₂) G φ (x , y) = (mapFold F₁ G φ x) , mapFold F₂ G φ y

open import Function using (_∘_)

fold : {F : Functor}{A : Set} → ([ F ] A → A) → μ F → A
fold {F} φ = φ ∘ mapFold F F φ ∘ out

NatF = |K| True |+| |Id|
Nat = μ NatF

Z : Nat
Z = In (inl (record {}))
S : Nat → Nat
S n = In (inr n)

ListF : Set → Functor
ListF A = |K| True |+| |K| A |x| |Id|
List : Set → Set
List A = μ (ListF A)

nil : {A : Set} → List A
nil = In (inl (record {}))
cons : {A : Set} → A → List A → List A
cons x xs = In (inr (x , xs))
