module Prelude.Validity where

open import Prelude.Init
open import Prelude.Decidable

-- record DecValidable (A : Set ℓ) ⦃ _ : Validable A ⦄ : Set (lsuc ℓ) where
--   field Valid? : Decidable¹ Valid
-- open DecValidable ⦃ ... ⦄ public

record Validable (A : Set ℓ) : Set (ℓ ⊔ₗ lsuc ℓ′) where
  field Valid : Pred A ℓ′

  Valid? : ⦃ Valid ⁇¹ ⦄ → Decidable¹ Valid
  Valid? _ = dec
open Validable ⦃ ... ⦄ public

-- record DecValidable (A : Set ℓ) : Set (lsuc ℓ) where
--   field
--     overlap ⦃ super ⦄ : Validable A
--     Valid? : Decidable¹ Valid
-- open DecValidable ⦃ ... ⦄ public

-- instance
--   DecValidable→Dec : ∀ {A : Set ℓ} ⦃ _ : DecValidable A ⦄ → {x : A} → (Valid x) ⁇
--   DecValidable→Dec .dec = Valid? _
