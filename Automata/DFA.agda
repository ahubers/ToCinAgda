module Automata.DFA where

open import Preludes.Data hiding (String)
open import Preludes.Relation

open import Data.List

--------------------------------------------------------------------------------
-- DFAs.

record DFA : Set₁ where
  field
    Q : Set
    ≡Q : Dec Q -- Need equivalence on Q to be decidable (see Firsov and Uustalu for business like this; may as well assert that Q is finite, too.)
    Σ : Set -- Ditto for Σ.
    δ : Q → Σ → Q
    F : List Q -- With Q and Σ properly "finite sets", I should be able to assert too that F ⊆ Q in a meaningful way.

(-- Also, while we're at it---it may be worthwhile to steal quite a lot from Firsov & Uustalu, as I am (in the theory of computation) almost exclusively considering the generation of infinite sets from tuples of finite descriptions.)
open DFA
open import Data.Bool

run : (D : DFA) → List (Σ D)  → Bool
run record { Q = Q ; ≡Q = ≡Q ; Σ = Σ ; δ = δ ; F = F } [] = any {!≡!} {!!}
run record { Q = Q ; ≡Q = ≡Q ; Σ = Σ ; δ = δ ; F = F } (x ∷ s) = {!!}
