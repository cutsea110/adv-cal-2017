module Universes where

open import Data.Bool
open import Data.Unit
open import Data.Empty

data Functor : Set₁ where
  |Id|  : Functor
  |K|   : Set → Functor
  _|+|_ : Functor → Functor → Functor
  _|x|_ : Functor → Functor → Functor

data _⊗_ (A B : Set) : Set where
  _,_ : A → B → A ⊗ B

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

infixr 50 _|+|_ _⊕_
infixr 60 _|x|_ _⊗_

-- F(X) = 1 + X
NatF : Functor
NatF = |K| ⊤ |+| |Id|

ListF : Set → Functor
ListF A = |K| ⊤ |+| |K| A |x| |Id|

[_] : Functor → Set → Set
[ |Id| ] X = X
[ |K| A ] X = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |x| G ] X = [ F ] X ⊗ [ G ] X


data μ (F : Functor) : Set where
  In : [ F ] (μ F) → μ F

out : {F : Functor} → μ F → [ F ] (μ F)
out (In x) = x

map : (F : Functor){X Y : Set} → (X → Y) → [ F ] X → [ F ] Y
map |Id| f x = f x
map (|K| A) f c = c
map (F |+| G) f (inl x) = inl (map F f x)
map (F |+| G) f (inr x) = inr (map G f x)
map (F |x| G) f (x , y) = map F f x , map G f y

open import Function using (_∘_)

-- Nat  => μ (|K| ⊤ |+| |Id|)
-- NatF =>    |K| ⊤ |+| |Id|
-- [ NatF ] Nat => ⊤ ⊕ μ (|K| ⊤ |+| |Id|) ≋ ⊤ ⊕ Nat
-- [ NatF ] (μ NatF) => ⊤ ⊕ μ (|K| ⊤ |+| |Id|)
Nat : Set
Nat = μ NatF

-- List Bool  => μ (|K| ⊤ |+| |K| Bool |x| |Id|)
-- ListF Bool =>    |K| ⊤ |+| |K| Bool |x| |Id|
-- [ ListF Bool ] (List Bool) => ⊤ ⊕ Bool ⊗ μ (|K| ⊤ |+| |K| Bool |x| |Id|) ≋ ⊤ ⊕ Bool ⊗ List Bool
-- [ ListF Bool ] (μ List Bool) => ⊤ ⊕ Bool ⊗ μ (|K| ⊤ |+| |K| Bool |x| |Id|)
List : Set → Set
List A = μ (ListF A)

--   F (μG)     μG <----------In------------ G (μG)
--     |         |                             |
--     |         |                             |
--     |         |                             |
--   u |       f |                             | G f
--     |         |                             |
--     |         |                             |
--     v         v                             v
--   F x         x <----------φ-------------  G x
mapFold : ∀ {X} F G → ([ G ] X → X) → [ F ] (μ G) → [ F ] X
mapFold |Id| H φ (In x) = φ (mapFold H H φ x)
mapFold (|K| A) H φ c = c
mapFold (F |+| G) H φ (inl x) = inl (mapFold F H φ x)
mapFold (F |+| G) H φ (inr x) = inr (mapFold G H φ x)
mapFold (F |x| G) H φ (x , y) = (mapFold F H φ x) , (mapFold G H φ y)

cata : ∀ {X} F → ([ F ] X → X) → μ F → X
cata F φ = φ ∘ map F (cata F φ) ∘ out
-- cata F φ = φ ∘ mapFold F F φ ∘ out


{--
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

[_||_] : {A B C : Set} → (A → C) → (B → C) → A ⊕ B → C
[ f || g ] (inl x) = f x
[ f || g ] (inr y) = g y

uncurry : {A B C : Set} → (A → B → C) → A ⊛ B → C
uncurry f (x , y) = f x y

const : {A B : Set} → A → B → A
const x y = x

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr {A} {B} f z = fold [ const z || uncurry f ]

plus : Nat → Nat → Nat
plus n m = fold [ const m || S ] n
--}
