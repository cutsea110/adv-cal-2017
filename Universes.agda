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

