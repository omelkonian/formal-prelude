{-# OPTIONS --safe #-}
module Prelude.PartialSemigroup where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Setoid
open import Prelude.Setoid.Maybe
open import Prelude.Semigroup
open import Prelude.Monad

record PartialSemigroup (A : Type ℓ) : Type ℓ where
  infixr 5 _◆_
  field _◆_ : A → A ⇀ A

  infix 4 _≫◆_ _◆≪_
  _≫◆_ : Maybe A → A ⇀ A
  m ≫◆ y = m >>= (_◆ y)

  _◆≪_ : A → Maybe A ⇀ A
  x ◆≪ m = (x ◆_) =<< m
open PartialSemigroup ⦃...⦄ public

record PartialSemigroupLaws
  (A : Type ℓ)
  ⦃ _ : PartialSemigroup A ⦄
  -- ⦃ _ : LawfulSetoid A ⦄
  ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
  : Type (ℓ ⊔ₗ relℓ {A = A})
  where
  field ◆-comm   : ∀ (x y : A) → x ◆ y ≈ y ◆ x
        ◆-assocʳ : ∀ (x y z : A) → (x ◆ y ≫◆ z) ≈ (x ◆≪ y ◆ z)
  ◆-assocˡ : ∀ (x y z : A) → (x ◆≪ y ◆ z) ≈ (x ◆ y ≫◆ z)
  ◆-assocˡ x y z = ≈-sym {x = _ ◆ _ ≫◆ _} $ ◆-assocʳ x y z
open PartialSemigroupLaws ⦃...⦄ public

PartialSemigroupLaws≡ : (A : Type ℓ) ⦃ _ : PartialSemigroup A ⦄ → Type ℓ
PartialSemigroupLaws≡ A = PartialSemigroupLaws A
  where instance _ = mkISetoid≡; _ = mkSetoidLaws≡

private variable A : Type ℓ; B : Type ℓ′

module _ ⦃ _ : Semigroup A ⦄ where
  Semigroup⇒Partial : PartialSemigroup A
  Semigroup⇒Partial ._◆_ = just ∘₂ _◇_
  instance _ = Semigroup⇒Partial

  SemigroupLaws⇒Partial
    : ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
    → ⦃ _ : SemigroupLaws A ⦄
    → PartialSemigroupLaws A
  SemigroupLaws⇒Partial = λ where .◆-comm → ◇-comm; .◆-assocʳ → ◇-assocʳ
