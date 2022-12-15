{-# OPTIONS --safe #-}
module Prelude.Validity where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable

-- record DecValidable (A : Type ℓ) ⦃ _ : Validable A ⦄ : Type (lsuc ℓ) where
--   field Valid? : Decidable¹ Valid
-- open DecValidable ⦃...⦄ public

record Validable (A : Type ℓ) : Type (ℓ ⊔ₗ lsuc ℓ′) where
  field Valid : Pred A ℓ′

  Valid? : ⦃ Valid ⁇¹ ⦄ → Decidable¹ Valid
  Valid? _ = dec

open Validable ⦃...⦄ public

-- record DecValidable (A : Type ℓ) : Type (lsuc ℓ) where
--   field
--     overlap ⦃ super ⦄ : Validable A
--     Valid? : Decidable¹ Valid
-- open DecValidable ⦃...⦄ public

-- instance
--   DecValidable→Dec : ∀ {A : Type ℓ} ⦃ _ : DecValidable A ⦄ → {x : A} → (Valid x) ⁇
--   DecValidable→Dec .dec = Valid? _

𝕍 : (A : Type ℓ) → ⦃ Validable {ℓ′ = ℓ′} A ⦄ → Type _
𝕍 A = ∃ λ (a : A) → Valid a
