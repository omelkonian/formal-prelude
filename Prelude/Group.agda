module Prelude.Group where

open import Prelude.Init
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Setoid

record Group (A : Set ℓ) : Set ℓ where
  field
    overlap ⦃ m ⦄ : Monoid A
    _⁻¹ : Op₁ A
open Group ⦃...⦄ public

record GroupLaws (A : Set ℓ) ⦃ _ : Group A ⦄ (_~_ : Rel A ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
  open Alg _~_
  field
    inverse : Inverse ε _⁻¹ _◇_
    ⁻¹-cong : Congruent₁ _⁻¹
open GroupLaws ⦃...⦄ public

GroupLaws≡ : (A : Set ℓ) ⦃ _ : Group A ⦄ → Set ℓ
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
module _ (G : Set ℓ) ⦃ _ : Group G ⦄ (X : Set ℓ′) ⦃ _ : ISetoid X ⦄ where

  record Actionˡ : Set (ℓ ⊔ₗ ℓ′ ⊔ₗ relℓ) where
    infixr 5 _·_
    field
      _·_ : G → X → X
      identity : ∀ {x : X} → ε · x ≈ x
      compatibility : ∀ {g h : G} {x : X} → g · h · x ≈ (g ◇ h) · x

  record Actionʳ : Set (ℓ ⊔ₗ ℓ′ ⊔ₗ relℓ) where
    infixl 5 _·_
    field
      _·_ : X → G → X
      identity : ∀ {x : X} → x · ε ≈ x
      compatibility : ∀ {x : X} {g h : G} → x · g · h ≈ x · (g ◇ h)

record GSet (G : Set ℓ) ⦃ _ : Group G ⦄ (X : Set ℓ′) ⦃ _ : ISetoid X ⦄ : Setω where
  field action : Actionˡ G X
open GSet public

record GSet′ (G : Set ℓ) ⦃ _ : Group G ⦄ : Setω where
  field
    {ℓₓ} : Level
    X : Set ℓₓ
    ⦃ setoidX ⦄ : ISetoid X
    action′ : Actionˡ G X
open GSet′ public
