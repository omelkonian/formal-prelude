module Prelude.Setoid where

open import Prelude.Init
open import Prelude.Decidable
-- open import Prelude.Equivalence

record ISetoid (A : Set ℓ) : Setω where
  infix 4 _≈_ _≉_
  field
    {relℓ} : Level
    _≈_ : Rel A relℓ

  _≉_ : Rel A relℓ
  x ≉ y = ¬ (x ≈ y)

  module _ ⦃ _ : _≈_ ⁇² ⦄ where
    infix 4 _≈?_ _≉?_
    _≈?_ : Decidable² _≈_
    _≈?_ = dec²
    _≉?_ : Decidable² _≉_
    _≉?_ = dec²
open ISetoid ⦃...⦄ public

IDecSetoid : ∀ (A : Set ℓ) ⦃ _ : ISetoid A ⦄ → Set (ℓ ⊔ₗ relℓ)
IDecSetoid A = _≈_ {A = A} ⁇²

record Setoid-Laws (A : Set ℓ) ⦃ _ : ISetoid A ⦄ : Setω where
  field isEquivalence : IsEquivalence _≈_
open Setoid-Laws ⦃...⦄ public

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