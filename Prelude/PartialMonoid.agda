module Prelude.PartialMonoid where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Setoid; import Prelude.Setoid.Maybe
open import Prelude.Semigroup
open import Prelude.PartialSemigroup
open import Prelude.Monoid
  hiding (ε-identity)
  renaming (ε to ε◇; ε-identityˡ to ε◇-identityˡ; ε-identityʳ to ε◇-identityʳ)

record PartialMonoid (A : Type ℓ) ⦃ _ : PartialSemigroup A ⦄ : Type ℓ where
  field ε : A
open PartialMonoid ⦃...⦄ public

record PartialMonoidLaws
  (A : Type ℓ)
  ⦃ _ : PartialSemigroup A ⦄
  ⦃ _ : PartialMonoid A ⦄
  ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
  : Type (ℓ ⊔ₗ relℓ {A = A})
  where
  field ε-identity : ∀ (x : A) → (ε ◆ x ≈ just x) × (x ◆ ε ≈ just x)

  ε-identityˡ : ∀ (x : A) → ε ◆ x ≈ just x
  ε-identityˡ = proj₁ ∘ ε-identity

  ε-identityʳ : ∀ (x : A) → x ◆ ε ≈ just x
  ε-identityʳ = proj₂ ∘ ε-identity
open PartialMonoidLaws ⦃...⦄ public

PartialMonoidLaws≡ : (A : Type ℓ) ⦃ _ : PartialSemigroup A ⦄
                   → ⦃ PartialMonoid A ⦄ → Type ℓ
PartialMonoidLaws≡ A = PartialMonoidLaws A
  where instance _ = mkISetoid≡; _ = mkSetoidLaws≡

private variable A : Type ℓ; B : Type ℓ′

module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ where
    instance _ = Semigroup⇒Partial
    Monoid⇒Partial : PartialMonoid A
    Monoid⇒Partial .ε = ε◇
    instance _ = Monoid⇒Partial

    MonoidLaws⇒Partial
      : ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
      → ⦃ _ : PartialSemigroupLaws A ⦄
      → ⦃ _ : MonoidLaws A ⦄
      → PartialMonoidLaws A
    MonoidLaws⇒Partial .ε-identity _ = ε◇-identityˡ _ , ε◇-identityʳ _
