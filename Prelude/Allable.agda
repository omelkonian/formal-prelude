module Prelude.Allable where

open import Prelude.Init hiding (All)

record Allable (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    All : ∀ {A} → Pred₀ A → F A → Set ℓ

  syntax All P xs = ∀[∈ xs ] P
  All′ = All
  syntax All′ (λ x → P) xs = ∀[ x ∈ xs ] P

open Allable ⦃ ... ⦄ public

instance
  Allable-List : Allable {ℓ} List
  Allable-List .All = L.All.All

private
  open import Prelude.Nary
  open import Prelude.Decidable

  _ : ∀[ x ∈ ⟦ 1 ,  2 , 3 ⟧ ] (x > 0)
  _ = auto
