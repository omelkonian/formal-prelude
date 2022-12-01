module Prelude.Setoid.Dec where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable.Core
open import Prelude.Setoid.Core

DecSetoid : ∀ (A : Type ℓ) ⦃ _ : ISetoid A ⦄ → Type (ℓ ⊔ₗ relℓ)
DecSetoid A = _≈_ {A = A} ⁇²

module _ {A : Type ℓ} ⦃ _ : ISetoid A ⦄ ⦃ _ : DecSetoid A ⦄ where
  infix 4 _≈?_ _≉?_
  _≈?_ : Decidable² _≈_
  _≈?_ = dec²
  _≉?_ : Decidable² _≉_
  _≉?_ = dec²
