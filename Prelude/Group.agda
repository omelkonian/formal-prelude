module Prelude.Group where

open import Prelude.Init; open SetAsType
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Setoid

record Group (A : Type ℓ) : Type ℓ where
  field
    overlap ⦃ m ⦄ : Monoid A
    _⁻¹ : Op₁ A
open Group ⦃...⦄ public

record GroupLaws (A : Type ℓ) ⦃ _ : Group A ⦄ (_~_ : Rel A ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  open Alg _~_
  field
    inverse : Inverse ε _⁻¹ _◇_
    ⁻¹-cong : Congruent₁ _⁻¹
open GroupLaws ⦃...⦄ public

GroupLaws≡ : (A : Type ℓ) ⦃ _ : Group A ⦄ → Type ℓ
GroupLaws≡ A = GroupLaws A _≡_

-- ** integers
module _ where
  open Integer

  Group-ℤ-+ = Group ℤ ∋ λ where ._⁻¹ → -_
    where instance _ = Monoid-ℤ-+
  GroupLaws-ℤ-+ = GroupLaws≡ ℤ ∋
    record {inverse = +-inverse ; ⁻¹-cong = cong (-_)}
    where instance _ = Group-ℤ-+

-- G-sets
module _ (G : Type ℓ) ⦃ _ : Group G ⦄ (X : Type ℓ′) ⦃ _ : ISetoid X ⦄ where

  record Actionˡ : Type (ℓ ⊔ₗ ℓ′ ⊔ₗ relℓ) where
    infixr 5 _·_
    field
      _·_ : G → X → X
      identity : ∀ {x : X} → ε · x ≈ x
      compatibility : ∀ {g h : G} {x : X} → g · h · x ≈ (g ◇ h) · x

  record Actionʳ : Type (ℓ ⊔ₗ ℓ′ ⊔ₗ relℓ) where
    infixl 5 _·_
    field
      _·_ : X → G → X
      identity : ∀ {x : X} → x · ε ≈ x
      compatibility : ∀ {x : X} {g h : G} → x · g · h ≈ x · (g ◇ h)

  open Actionˡ ⦃...⦄ public renaming
    (identity to ·-identity; compatibility to ·-compatibility)

record GSet (G : Type ℓ) ⦃ _ : Group G ⦄ (X : Type ℓ′) ⦃ _ : ISetoid X ⦄ : Typeω where
  field ⦃ action ⦄ : Actionˡ G X
open GSet ⦃...⦄ public

record GSet′ (G : Type ℓ) ⦃ _ : Group G ⦄ : Typeω where
  field
    {ℓₓ} : Level
    X : Type ℓₓ
    ⦃ setoidX ⦄ : ISetoid X
    action′ : Actionˡ G X
open GSet′ public

module GSet-Morphisms (G : Type ℓ) ⦃ _ : Group G ⦄ where

  module _ (X Y : Type ℓ′) ⦃ _ : ISetoid X ⦄ ⦃ _ : ISetoid Y ⦄ ⦃ _ : GSet G X ⦄ ⦃ _ : GSet G Y ⦄ where

    record _—𝔾→_ : Type (ℓ ⊔ₗ ℓ′ ⊔ₗ relℓ) where
      field
        F : X → Y
        equivariant : ∀ {g : G} {x : X} → F (g · x) ≈ g · F x
    open _—𝔾→_ public renaming (F to _𝔾⟨$⟩_)
