module Prelude.Setoid where

open import Prelude.Init
open import Prelude.Decidable

record ISetoid (A : Set ℓ) : Set (lsuc ℓ) where
  infix 4 _≈_ _≉_
  field _≈_ : Rel₀ A

  _≉_ : Rel₀ A
  x ≉ y = ¬ (x ≈ y)

  module _ ⦃ _ : _≈_ ⁇² ⦄ where
    infix 4 _≈?_ _≉?_
    _≈?_ : Decidable² _≈_
    _≈?_ = dec²
    _≉?_ : Decidable² _≉_
    _≉?_ = dec²
open ISetoid ⦃ ... ⦄ public

IDecSetoid : (A : Set ℓ) → ⦃ ISetoid A ⦄ → Set ℓ
IDecSetoid A = _≈_ {A = A} ⁇²

{-
record IDecSetoid (A : Set ℓ) ⦃ _ : ISetoid A ⦄ : Set (lsuc ℓ) where
  infix 4 _≈?_ _≉?_
  field _≈?_ : Decidable² _≈_

  _≉?_ : Decidable² _≉_
  x ≉? y = ¬? (x ≈? y)
open IDecSetoid ⦃ ... ⦄ public

instance
  Decide-Setoid : ∀ {A : Set ℓ} ⦃ _ : ISetoid A ⦄ → ⦃ _≈_ ⁇² ⦄ → IDecSetoid A
  Decide-Setoid ._≈?_ = dec²
-}
