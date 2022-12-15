{-# OPTIONS --safe #-}
module Prelude.Irrelevance.Core where

open import Prelude.Init; open SetAsType

private variable A B : Type ℓ; P : A → Type ℓ

-- A type is squashed when all of its values are equal.
record ·_ (A : Type ℓ) : Type ℓ where
  field ∀≡ : Irrelevant A

  _∀≡↝_ : ∃ P → (x : A) → P x
  _∀≡↝_ (y , p) x rewrite ∀≡ y x = p

  -- A dependent product indexed by a squashed type is decidable!
  -- T0D0: generalize to enumerable indices
  _∃-dec_ : Dec A → (∀ a → Dec (P a)) → Dec (Product.Σ A P)
  a? ∃-dec b?
    with a?
  ... | no ¬a  = no $ ¬a ∘ proj₁
  ... | yes a✓
    with b? a✓
  ... | no ¬b  = no $ ¬b ∘ (_∀≡↝ a✓)
  ... | yes b✓ = yes (a✓ , b✓)
open ·_ ⦃...⦄ public

·¹_ : ∀ {A : Type ℓ} → Pred A ℓ′ → Type (ℓ ⊔ₗ ℓ′)
·¹ P = ∀ {x} → · P x

·²_ : ∀ {A B : Type ℓ} → REL A B ℓ′ → Type (ℓ ⊔ₗ ℓ′)
·² _~_ = ∀ {x y} → · (x ~ y)

·³_ : ∀ {A B C : Type ℓ} → 3REL A B C ℓ′ → Type (ℓ ⊔ₗ ℓ′)
·³ _~_~_ = ∀ {x y z} → · (x ~ y ~ z)

instance
  ·-⊥ : · ⊥
  ·-⊥ .∀≡ ()

  ·-⊤ : · ⊤
  ·-⊤ .∀≡ tt tt = refl

  ·-× : ⦃ · A ⦄ → ⦃ · B ⦄ → · (A × B)
  ·-× .∀≡ (x , y) (x′ , y′) rewrite ∀≡ x x′ | ∀≡ y y′ = refl
