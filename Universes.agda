module Universes where

-- a type of codes
data Bool : Set where
  true  : Bool
  false : Bool

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where


-- decoding function
isTrue : Bool → Set
isTrue true = ⊤
isTrue false = ⊥

--------------------------
-- a type of code
data Functor : Set₁ where
  |I| : Functor
  |K| : Set → Functor
  _|+|_ : Functor → Functor → Functor
  _|x|_ : Functor → Functor → Functor

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

data _⊗_ (A B : Set) : Set where
  _,_ : A → B → A ⊗ B

infixr 50 _|+|_ _⊕_
infixr 60 _|x|_ _⊗_

-- decoding function
[_] : (F : Functor) → Set → Set
[ |I| ] X = X
[ |K| A ] X = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |x| G ] X = [ F ] X ⊗ [ G ] X

NatF : Functor
NatF = |K| ⊤ |+| |I|

ListF : Set → Functor
ListF A = |K| ⊤ |+| |K| A |x| |I|

-- newtype Mu f = In { out :: f (Mu f) }
data μ (F : Functor) : Set where
  In : [ F ] (μ F) → μ F

Nat : Set
Nat = μ NatF
List : Set → Set
List A = μ (ListF A)

out : {F : Functor} → μ F → [ F ] (μ F)
out (In x) = x

-- A      FA
-- |f     |Ff
-- v      v   
-- B      FB

-- type functor
map : (F : Functor){A B : Set} → (A → B) → [ F ] A → [ F ] B
map |I| f x = f x
map (|K| A) f c = c
map (F₁ |+| F₂) f (inl x) = inl (map F₁ f x)
map (F₁ |+| F₂) f (inr x) = inr (map F₂ f x)
map (F₁ |x| F₂) f (x₁ , x₂) = (map F₁ f x₁) , (map F₂ f x₂)

--        In
-- μF <------- F(μF)
-- |            |
-- |u = cata φ  | Fu = F(cata φ)
-- |            |
-- v            v
-- X  <------- FX
--        φ

open import Function using (_∘_)


--                  In
-- F(μG)    μG <------- G(μG)
--  |       |            |
--  |       |u = cata φ  | Gu = G(cata φ)
--  |       |            |
--  v       v            v
-- FX       X  <------- GX
--                 φ

mapCata : (F G : Functor){X : Set} → ([ G ] X → X) → [ F ] (μ G) → [ F ] X
mapCata |I| G φ (In x) = φ (mapCata G G φ x)
mapCata (|K| A) G φ c = c
mapCata (F₁ |+| F₂) G φ (inl x) = inl (mapCata F₁ G φ x)
mapCata (F₁ |+| F₂) G φ (inr x) = inr (mapCata F₂ G φ x)
mapCata (F₁ |x| F₂) G φ (x₁ , x₂) = mapCata F₁ G φ x₁ , mapCata F₂ G φ x₂

cata : (F : Functor){X : Set} → ([ F ] X → X) →  μ F → X
cata F φ = φ ∘ mapCata F F φ  ∘ out

zero : Nat
zero = In (inl tt)
succ : Nat → Nat
succ n = In (inr n)

nil : {A : Set} → List A
nil = In (inl tt)
cons : {A : Set} → A → List A → List A
cons x xs = In (inr (x , xs))

either : {A B C : Set} → (A → C) → (B → C) → (A ⊕ B) → C
either f g (inl x) = f x
either f g (inr x) = g x
const : {A B : Set} → A → B → A
const x y = x
uncurry : {A B C : Set} → (A → B → C) → (A ⊗ B) → C
uncurry f (x , y) = f x y

foldr : ∀ {A B} → (A → B → B) → B → List A → B
foldr {A} f z = cata (ListF A) (either (const z) (uncurry f))

plus : Nat → Nat → Nat
plus n m = cata NatF (either (const m) succ) n
