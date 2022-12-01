module Prelude.Group where

open import Prelude.Init; open SetAsType
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Setoid

record Group (A : Type ℓ) ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ : Type ℓ where
  field _⁻¹ : Op₁ A
open Group ⦃...⦄ public

record GroupLaws (A : Type ℓ)
  -- ⦃ _ : LawfulSetoid A ⦄
  ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
  ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ ⦃ _ : Group A ⦄
  : Type (ℓ ⊔ₗ relℓ) where
  open Alg≈
  field
    inverse : Inverse ε _⁻¹ _◇_
    ⁻¹-cong : Congruent₁ _⁻¹
open GroupLaws ⦃...⦄ public

GroupLaws≡ : (A : Type ℓ)
  ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ ⦃ _ : Group A ⦄ → Type ℓ
GroupLaws≡ A = GroupLaws A
  where instance _ = mkISetoid≡; _ = mkSetoidLaws≡

-- ** integers
module _ where
  open Integer

  instance _ = mkISetoid≡; _ = mkSetoidLaws≡
           _ = Semigroup-ℤ-+
           _ = Monoid-ℤ-+
  Group-ℤ-+ = Group ℤ ∋ λ where ._⁻¹ → -_
  instance _ = Group-ℤ-+
  GroupLaws-ℤ-+ = GroupLaws≡ ℤ ∋ record {inverse = +-inverse ; ⁻¹-cong = cong (-_)}

-- G-sets
module _ (G : Type ℓ) ⦃ _ : Semigroup G ⦄ ⦃ _ : Monoid G ⦄ ⦃ _ : Group G ⦄ where

  module _ (X : Type ℓ′) ⦃ _ : ISetoid X ⦄ where
    record Actionˡ : Type (ℓ ⊔ₗ ℓ′ ⊔ₗ relℓ) where
      infixr 5 _·_
      field _·_ : G → X → X
            identity : ∀ {x : X} → ε · x ≈ x
            compatibility : ∀ {g h : G} {x : X} → g · h · x ≈ (g ◇ h) · x
    record Actionʳ : Type (ℓ ⊔ₗ ℓ′ ⊔ₗ relℓ) where
      infixl 5 _·_
      field _·_ : X → G → X
            identity : ∀ {x : X} → x · ε ≈ x
            compatibility : ∀ {x : X} {g h : G} → x · g · h ≈ x · (g ◇ h)
    open Actionˡ ⦃...⦄ public renaming
      (identity to ·-identity; compatibility to ·-compatibility)

    record GSet : Typeω where
      field ⦃ action ⦄ : Actionˡ
    open GSet ⦃...⦄ public

  record GSet′ : Typeω where
    field
      {ℓₓ} : Level
      X : Type ℓₓ
      ⦃ setoidX ⦄ : ISetoid X
      action′ : Actionˡ X
  open GSet′ public

  module GSet-Morphisms (X Y : Type ℓ′)
    ⦃ _ : ISetoid X ⦄ ⦃ _ : ISetoid Y ⦄
    ⦃ _ : GSet X ⦄ ⦃ _ : GSet Y ⦄ where
    record _—𝔾→_ : Type (ℓ ⊔ₗ ℓ′ ⊔ₗ relℓ) where
      field
        F : X → Y
        equivariant : ∀ {g : G} {x : X} → F (g · x) ≈ g · F x
    open _—𝔾→_ public renaming (F to _𝔾⟨$⟩_)
