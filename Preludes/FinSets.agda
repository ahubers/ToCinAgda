module Preludes.FinSets where

open import Preludes.Data
open import Preludes.Relation

open import Data.List.Membership.Propositional

--------------------------------------------------------------------------------
--

All : (X : Set) → List X → Set
All X xs = ∀ (x : X) → x ∈ xs

Listable : ∀ (X : Set) → Set
Listable X = Σ[ xs ∈ List X ] (All X xs)


DecEq : ∀ (X : Set) → Set
DecEq X = ∀ (x y : X) → Dec (x ≡ y)
