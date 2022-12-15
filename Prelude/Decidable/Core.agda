{-# OPTIONS --safe #-}
module Prelude.Decidable.Core where

open import Prelude.Init; open SetAsType

record _⁇ (P : Type ℓ) : Type ℓ where
  constructor ⁇_
  field dec : Dec P

  auto : ⦃ True dec ⦄ → P
  auto ⦃ pr ⦄ = toWitness pr

  -- NB: already covered by `auto`
  -- ¬auto : ∀ {pr : False dec} → ¬ P
  -- ¬auto {pr} = toWitnessFalse pr

  contradict : ∀ {X : Type} {pr : False dec} → P → X
  contradict {pr = pr} = ⊥-elim ∘ toWitnessFalse pr

open _⁇ ⦃ ... ⦄ public

¿_¿ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Dec X
¿ _ ¿ = dec

_⁇¹ : ∀ {A : Type ℓ} → (P : Pred A ℓ′) → Type (ℓ ⊔ₗ ℓ′)
P ⁇¹ = ∀ {x} → P x ⁇

dec¹ : ∀ {A : Type ℓ} {P : Pred A ℓ′} → ⦃ P ⁇¹ ⦄ → Decidable¹ P
dec¹ _ = dec

¿_¿¹ : ∀ {A : Type ℓ} (P : Pred A ℓ′) → ⦃ P ⁇¹ ⦄ → Decidable¹ P
¿ _ ¿¹ = dec¹

_⁇² : ∀ {A B : Type ℓ} → (P : REL A B ℓ′) → Type (ℓ ⊔ₗ ℓ′)
_~_ ⁇² = ∀ {x y} → (x ~ y) ⁇

dec² : ∀ {A B : Type ℓ} {_~_ : REL A B ℓ′} → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
dec² _ _ = dec

¿_¿² : ∀ {A B : Type ℓ} (_~_ : REL A B ℓ′) → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
¿ _ ¿² = dec²

_⁇³ : ∀ {A B C : Type ℓ} → (P : 3REL A B C ℓ′) → Type (ℓ ⊔ₗ ℓ′)
_~_~_ ⁇³ = ∀ {x y z} → (x ~ y ~ z) ⁇

dec³ : ∀ {A B C : Type ℓ} {_~_~_ : 3REL A B C ℓ′} → ⦃ _~_~_ ⁇³ ⦄ → Decidable³ _~_~_
dec³ _ _ _ = dec

¿_¿³ : ∀ {A B C : Type ℓ} (_~_~_ : 3REL A B C ℓ′) → ⦃ _~_~_ ⁇³ ⦄ → Decidable³ _~_~_
¿ _ ¿³ = dec³

infix -100 auto∶_
auto∶_ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Type
auto∶_ A = True ¿ A ¿

-- ** basic instances

private variable A : Type ℓ; B : Type ℓ′
instance
  Dec-⊥ : ⊥ ⁇
  Dec-⊥ .dec = no λ()

  Dec-⊤ : ⊤ ⁇
  Dec-⊤ .dec = yes tt

  Dec-→ : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A → B) ⁇
  Dec-→ .dec = dec →-dec dec

  -- NB: Already covered by implication
  -- Dec-¬ : ⦃ A ⁇ ⦄ → (¬ A) ⁇
  -- Dec-¬ .dec = ¬? dec

  Dec-× : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A × B) ⁇
  Dec-× .dec = dec ×-dec dec

  Dec-⊎ : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A ⊎ B) ⁇
  Dec-⊎ .dec = dec ⊎-dec dec
