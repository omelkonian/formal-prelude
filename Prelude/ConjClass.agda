-- ** Conjuctive classes: gather up different instances together
module Prelude.ConjClass where

open import Prelude.Init; open SetAsType

private variable A : Type ℓ; B : Type ℓ′

infixr -100 _⊗_
record _⊗_ (A : Type ℓ) (B : ⦃ A ⦄ → Type ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  field ⦃ ↜ ⦄ : A
  field ⦃ ↝ ⦄ : B
instance
  mk⊗ : ⦃ A ⦄ → ⦃ _ : B ⦄ → A ⊗ B
  mk⊗ = record {}
open _⊗_ ⦃...⦄ hiding (↜; ↝)

private
  record X (A : Type ℓ) : Type ℓ where
    field x : A
  open X ⦃...⦄
  record Y (A : Type ℓ) : Type ℓ where
    field
      overlap ⦃ super ⦄ : X A
      y : A
      x≡y : x ≡ y
  open Y ⦃...⦄
  record Y′ (A : Type ℓ) ⦃ _ : X A ⦄ : Type ℓ where
    field y′ : A
          x≡y′ : x ≡ y′
  open Y′ ⦃...⦄
  record Z (A : Type ℓ) : Type ℓ where
    field
      overlap ⦃ super ⦄ : X A
      z : A
      x≡z : x ≡ z
  open Z ⦃...⦄

  module _ ⦃ _ : Y A ⦄ ⦃ _ : Y′ A ⦄ ⦃ _ : Z A ⦄ where
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , y , x≡y
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , y′ , x≡y′
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , z , x≡z
  module _ ⦃ _ : Y A ⊗ Y′ A ⊗ Z A ⦄ where
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , y , x≡y
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , y′ , x≡y′
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , z , x≡z
  module _ ⦃ _ : Y A ⦄ ⦃ _ : Y′ A ⦄ ⦃ _ : Z A ⦄ where
    _ : X A
    _ = it
    _ : X A ⊗ Y A
    _ = it
    _ : X A ⊗ Z A
    _ = it
    _ : X A ⊗ Y′ A
    _ = it
    _ : Y A ⊗ Y′ A ⊗ Z A
    _ = it
    _ : X A ⊗ Y A ⊗ Z A
    _ = it
    _ : X A ⊗ Y′ A ⊗ Z A
    _ = it
    _ : X A ⊗ Y A ⊗ Y′ A ⊗ Z A
    _ = it
