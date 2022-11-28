module Prelude.Irrelevance.Product where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable

open import Prelude.Irrelevance.Core

private variable
  A : Type ℓ
  B : Type ℓ′
  P : A → Type ℓ″

-- instance
Dec-Σ : ⦃ _ : · A ⦄ ⦃ _ : A ⁇ ⦄ ⦃ _ : ∀ {x} → P x ⁇ ⦄ → Σ A P ⁇
Dec-Σ .dec = dec ∃-dec λ _ → dec

-- ** Products with erased proj₂, aka refinements.

record Σ₀ (A : Type ℓ) (P : A → Type ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  constructor _,₀_
  field
    element   : A
    .property : P element
open Σ₀ public
infixr 4 _,₀_

infixr 2 _×₀_

_×₀_ : ∀ (A : Type ℓ) (B : Type ℓ′) → Type (ℓ ⊔ₗ ℓ′)
A ×₀ B = Σ₀ A (const B)

∃₀ : ∀ {A : Type ℓ} → (A → Type ℓ′) → Type (ℓ ⊔ₗ ℓ′)
∃₀ = Σ₀ _
