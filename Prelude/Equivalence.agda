module Prelude.Equivalence where

open import Prelude.Init

record PartialEquivalence {A : Set ℓ} (_≈_ : Rel A ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
  field
    ≈-sym′   : Symmetric _≈_
    ≈-trans′ : Transitive _≈_
open PartialEquivalence ⦃ ... ⦄ public

record Equivalence {A : Set ℓ} (_≈_ : Rel A ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
  field
    ≈-refl  : Reflexive _≈_
    ≈-sym   : Symmetric _≈_
    ≈-trans : Transitive _≈_
open Equivalence ⦃ ... ⦄ public

-- open import Prelude.Decidable
-- module _ {A : Set ℓ} {_≈_ : Rel A ℓ′} ⦃ _ : Equivalence _≈_ ⦄ ⟦ where
--   _
