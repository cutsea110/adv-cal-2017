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

--------------

-- a type of codes
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
[ |K| C ] X = C
[ F₁ |+| F₂ ] X = [ F₁ ] X ⊕ [ F₂ ] X
[ F₁ |x| F₂ ] X = [ F₁ ] X ⊗ [ F₂ ] X

-- newtype Fix f = In { out :: f (Fix f) }
-- type Fix f = f (Fix f)
data μ (F : Functor) : Set where
  In : [ F ] (μ F) → μ F

out : {F : Functor} → μ F → [ F ] (μ F)
out (In x) = x

NatF : Functor
NatF = |K| ⊤ |+| |I|
Nat : Set
Nat = μ NatF
zero : Nat
zero = In (inl tt)
succ : Nat → Nat
succ n = In (inr n)

ListF : Set → Functor
ListF A = |K| ⊤ |+| |K| A |x| |I|
List : Set → Set
List A = μ (ListF A)
nil : {A : Set} → List A
nil = In (inl tt)
cons : {A : Set} → A → List A → List A
cons x xs = In (inr (x , xs))

-- A ----> FA
-- |f      |Ff
-- v       v
-- B ----> FB

map : (F : Functor){A B : Set} → (A → B) → [ F ] A → [ F ] B
map |I| f x = f x
map (|K| C) f c = c
map (F₁ |+| F₂) f (inl x) = inl (map F₁ f x)
map (F₁ |+| F₂) f (inr x) = inr (map F₂ f x)
map (F₁ |x| F₂) f (x₁ , x₂) = map F₁ f x₁ , map F₂ f x₂

open import Function using (_∘_)

--                  In
-- F(μG)     μG <------- G(μG)
--  |        |  ------->  |
--  |        |     out    |
--  |        |u           |Fu
--  |        |            |
--  v        v            v
-- F(X)      X  <------- G(X)
--                 φ
mapCata : (F G : Functor){X : Set} → ([ G ] X → X) → [ F ] (μ G) → [ F ] X
mapCata |I| G φ (In x) = φ (mapCata G G φ x)
mapCata (|K| C) G φ c = c
mapCata (F₁ |+| F₂) G φ (inl x) = inl (mapCata F₁ G φ x)
mapCata (F₁ |+| F₂) G φ (inr x) = inr (mapCata F₂ G φ x)
mapCata (F₁ |x| F₂) G φ (x₁ , x₂) = mapCata F₁ G φ x₁ , mapCata F₂ G φ x₂

--        In
-- μF <------- F(μF)
-- |  ------->  |
-- |     out    |
-- |u           |Fu
-- |            |
-- v            v
-- X  <------- F(X)
--       φ

cata : (F : Functor){X : Set} → ([ F ] X → X) → μ F → X
cata F φ =  φ ∘ mapCata F F φ ∘ out

pair : {A B C : Set} → ((A → B) ⊗ (A → C)) → A → B ⊗ C
pair (f , g) x = (f x , g x)

either : {A B C : Set} → (A → C) → (B → C) → A ⊕ B → C
either f g (inl x) = f x
either f g (inr x) = g x

id : {A : Set} → A → A
id x = x

const : {A B : Set} → A → B → A
const x y = x

uncurry : {A B C : Set} → (A → B → C) → A ⊗ B → C
uncurry f (x , y) = f x y

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr {A} f b = cata (ListF A) (either (const b) (uncurry f))

foldn : {A : Set} → (A → A) → A → Nat → A
foldn f n = cata NatF (either (const n) f)

plus : Nat → Nat → Nat
plus = foldn succ
mult : Nat → Nat → Nat
mult n = foldn (plus n) zero
expr : Nat → Nat → Nat
expr n = foldn (mult n) (succ zero)

open import Data.Nat renaming (zero to Z; suc to S)

-- utility
fromNat : Nat → ℕ
fromNat (In (inl tt)) = 0
fromNat (In (inr x)) = S (fromNat x)

toNat : ℕ → Nat
toNat Z = zero
toNat (S n) = succ (toNat n)

mapPara : (F G : Functor){X : Set} → ([ G ] (μ G ⊗ X) → X) → [ F ] (μ G) → [ F ] (μ F ⊗ X)
mapPara F G φ x = {!!}

para : (F : Functor){X : Set} → ([ F ] (μ F ⊗ X) → X) → μ F → X
-- para F φ = φ ∘ map F (pair (id , para F φ)) ∘ out
para F φ = φ ∘  mapPara F F φ  ∘ out
