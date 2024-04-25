module Automata.DFA where

open import Preludes.Data hiding (String)
open import Preludes.Relation
open import Preludes.FinSets

open import Data.List.Membership.Propositional

--------------------------------------------------------------------------------
-- DFAs.

record DFA : Set₁ where
  field
    Q : Set
    LQ : Listable Q
    ≡Q : DecEq Q  -- implies membership is decidable. Is decidable equality implied by finiteness?

    q₀ : Q

    Σ : Set 
    LΣ : Listable Σ
    ≡Σ : DecEq Σ -- implies membership is decidable.

    δ : Q → Σ → Q
    F : List Q 


open DFA
open import Data.Bool

module Pfft (D : DFA) where
  run : (q : Q D) → List (Σ D) → Set
  run q [] = {!q ∈? F!}  -- Need Decidable membership check. (Which follows from Decidable equality, but I don't have the lemma on hand.)
  run q (x ∷ xs) = run (δ D q x) xs 
