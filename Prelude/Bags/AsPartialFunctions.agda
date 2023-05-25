{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Applicative
open import Prelude.Decidable
open import Prelude.Apartness
open import Prelude.InferenceRules
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Functor
open import Prelude.Ord
open import Prelude.Setoid

import Relation.Binary.Reasoning.Setoid as BinSetoid

module Prelude.Bags.AsPartialFunctions {A : Type} where

Bag : Type
Bag = A → Maybe ℕ

syntax Bag {A = A} = Bag⟨ A ⟩

∅ : Bag
∅ = const nothing

infix 3 _∈ᵈ_ _∉ᵈ_ _∈ᵈ?_ _∉ᵈ?_
_∈ᵈ_ _∉ᵈ_ : A → Bag → Type
k ∈ᵈ m = M.Any.Any (_> 0) (m k)
k ∉ᵈ m = ¬ (k ∈ᵈ m)

_∈ᵈ?_ : Decidable² _∈ᵈ_
k ∈ᵈ? m = M.Any.dec (_>? 0) (m k)

_∉ᵈ?_ : Decidable² _∉ᵈ_
k ∉ᵈ? m = ¬? (k ∈ᵈ? m)

infix 3 _⊆ᵈ_ _⊈ᵈ_
_⊆ᵈ_ _⊈ᵈ_ : Rel₀ Bag
m ⊆ᵈ m′ = ∀ k → k ∈ᵈ m → k ∈ᵈ m′
k ⊈ᵈ m = ¬ (k ⊆ᵈ m)

-- ** equivalence

instance
  Setoid-Bag : ISetoid Bag
  Setoid-Bag = λ where
    .relℓ → _
    ._≈_ m m′ → ∀ k → m k ≡ m′ k

  SetoidLaws-Bag : SetoidLaws Bag
  SetoidLaws-Bag .isEquivalence = record
    { refl = λ _ → refl
    ; sym = λ p k → sym (p k)
    ; trans = λ p q k → trans (p k) (q k)
    }
