module Universes where

data ⊤ : Set where
  tt : ⊤

data _⊗_ (A B : Set) : Set where
  _,_ : A → B → A ⊗ B

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

data Functor : Set₁ where
  |I|   : Functor
  |K|   : Set → Functor
  _|+|_ : Functor → Functor → Functor
  _|x|_ : Functor → Functor → Functor

infixr 50 _|+|_ _⊕_
infixr 60 _|x|_ _⊗_

-- F(X) = 1 + X
NatF : Functor
NatF = |K| ⊤ |+| |I|

ListF : Set → Functor
ListF A = |K| ⊤ |+| |K| A |x| |I|

[_] : Functor → Set → Set
[ |I| ] X = X
[ |K| A ] X = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |x| G ] X = [ F ] X ⊗ [ G ] X


data μ (F : Functor) : Set where
  In : [ F ] (μ F) → μ F

out : {F : Functor} → μ F → [ F ] (μ F)
out (In x) = x

map : (F : Functor){X Y : Set} → (X → Y) → [ F ] X → [ F ] Y
map |I| f x = f x
map (|K| A) f c = c
map (F |+| G) f (inl x) = inl (map F f x)
map (F |+| G) f (inr x) = inr (map G f x)
map (F |x| G) f (x , y) = map F f x , map G f y

open import Function using (_∘_)

-- Nat  => μ (|K| ⊤ |+| |I|)
-- NatF =>    |K| ⊤ |+| |I|
-- [ NatF ] Nat => ⊤ ⊕ μ (|K| ⊤ |+| |I|) ≋ ⊤ ⊕ Nat
-- [ NatF ] (μ NatF) => ⊤ ⊕ μ (|K| ⊤ |+| |I|)
Nat : Set
Nat = μ NatF

-- List Bool  => μ (|K| ⊤ |+| |K| Bool |x| |I|)
-- ListF Bool =>    |K| ⊤ |+| |K| Bool |x| |I|
-- [ ListF Bool ] (List Bool) => ⊤ ⊕ Bool ⊗ μ (|K| ⊤ |+| |K| Bool |x| |I|) ≋ ⊤ ⊕ Bool ⊗ List Bool
-- [ ListF Bool ] (μ List Bool) => ⊤ ⊕ Bool ⊗ μ (|K| ⊤ |+| |K| Bool |x| |I|)
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
mapFold |I| H φ (In x) = φ (mapFold H H φ x)
mapFold (|K| A) H φ c = c
mapFold (F |+| G) H φ (inl x) = inl (mapFold F H φ x)
mapFold (F |+| G) H φ (inr x) = inr (mapFold G H φ x)
mapFold (F |x| G) H φ (x , y) = (mapFold F H φ x) , (mapFold G H φ y)

cata : ∀ {X} F → ([ F ] X → X) → μ F → X
-- cata F φ = φ ∘ map F (cata F φ) ∘ out
cata F φ = φ ∘ mapFold F F φ ∘ out

zero : Nat
zero = In (inl tt)
succ : Nat → Nat
succ n = In (inr n)

nil : {A : Set} → List A
nil = In (inl tt)
cons : {A : Set} → A → List A → List A
cons x xs = In (inr (x , xs))

either : {A B C : Set} → (A → C) → (B → C) → A ⊕ B → C
either f g (inl x) = f x
either f g (inr x) = g x

uncurry : {A B C : Set} → (A → B → C) → A ⊗ B → C
uncurry f (x , y) = f x y

const : {A B : Set} → A → B → A
const x y = x

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr {A} f z = cata (ListF A) (either (const z) (uncurry f))

plus : Nat → Nat → Nat
plus n m = cata NatF (either (const m) succ) n
