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

  open IsEquivalence isEquivalence public
    renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans; reflexive to ≈-reflexive)

  mkSetoid : Setoid ℓ relℓ
  mkSetoid = record {Carrier = A; _≈_ = _≈_; isEquivalence = isEquivalence}

  import Relation.Binary.Reasoning.Setoid as BinSetoid
  module ≈-Reasoning = BinSetoid mkSetoid
open Setoid-Laws ⦃...⦄ public

record Lawful-Setoid (A : Set ℓ) : Setω where
  field
    ⦃ isSetoid ⦄ : ISetoid A
    ⦃ hasSetoidLaws ⦄ : Setoid-Laws A
open Lawful-Setoid ⦃...⦄ using () public

instance
  mkLawful-Setoid : {A : Set ℓ} ⦃ _ : ISetoid A ⦄ → ⦃ Setoid-Laws A ⦄ → Lawful-Setoid A
  mkLawful-Setoid = record {}

_⟶_ : (A : Set ℓ) (B : Set ℓ′) ⦃ _ : Lawful-Setoid A ⦄ ⦃ _ : Lawful-Setoid B ⦄ → Set _
A ⟶ B = mkSetoid {A = A} Fun.Eq.⟶ mkSetoid {A = B}

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
