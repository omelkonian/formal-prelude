module Prelude.Lists.SetEquality where

open import Data.List.Relation.Binary.BagAndSetEquality

open import Prelude.Init
open L.Mem
open import Prelude.InferenceRules
open import Prelude.DecLists
open import Prelude.DecEq
open import Prelude.Lists.Core
open import Prelude.Lists.Membership

private variable
  A : Set ℓ; B : Set ℓ′
  xs ys : List A

_∼[set]_ : Rel (List A) _
_∼[set]_ = _∼[ set ]_

_⊆⊇_ : Rel (List A) _
xs ⊆⊇ ys = (xs ⊆ ys) × (ys ⊆ xs)

module _ where
  open Fun.Equiv.Equivalence

  ⊆⊇⇒~set : ∀ {A : Set} {xs ys : List A} →
    xs ⊆⊇ ys
    ────────────
    xs ∼[set] ys
  ⊆⊇⇒~set {xs = xs}{ys} (↝ , ↜) = λ where
    .to   → record {_⟨$⟩_ = ↝; cong = λ where refl → refl}
    .from → record {_⟨$⟩_ = ↜; cong = λ where refl → refl}

  ~set⇒⊆⊇ :
    xs ∼[set] ys
    ────────────
    xs ⊆⊇ ys
  ~set⇒⊆⊇ {xs = xs}{ys} eq = eq .to .Fun.Eq._⟨$⟩_ , eq .from .Fun.Eq._⟨$⟩_

nub-seteq : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {xs : List A} →
  nub xs ∼[set] xs
nub-seteq = ⊆⊇⇒~set (∈-nub⁻ , ∈-nub⁺)

lefts-seteq : ∀ {A B : Set} {abs abs′ : List (A ⊎ B)} →
        abs ∼[set] abs′
  ───────────────────────────
  lefts abs ∼[set] lefts abs′
lefts-seteq eq = let ↝ , ↜ = ~set⇒⊆⊇ eq in
  ⊆⊇⇒~set (∈-lefts⁺ ∘ ↝ ∘ ∈-lefts⁻ , ∈-lefts⁺ ∘ ↜ ∘ ∈-lefts⁻)

rights-seteq : ∀ {A B : Set} {abs abs′ : List (A ⊎ B)} →
        abs ∼[set] abs′
  ───────────────────────────
  rights abs ∼[set] rights abs′
rights-seteq eq = let ↝ , ↜ = ~set⇒⊆⊇ eq in
  ⊆⊇⇒~set (∈-rights⁺ ∘ ↝ ∘ ∈-rights⁻ , ∈-rights⁺ ∘ ↜ ∘ ∈-rights⁻)
