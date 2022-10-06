module Prelude.Decidable.Base where

open import Prelude.Init

record _⁇ (P : Set ℓ) : Set ℓ where
  constructor ⁇_
  field dec : Dec P

  auto : ⦃ True dec ⦄ → P
  auto ⦃ pr ⦄ = toWitness pr

  -- NB: already covered by `auto`
  -- ¬auto : ∀ {pr : False dec} → ¬ P
  -- ¬auto {pr} = toWitnessFalse pr

  contradict : ∀ {X : Set} {pr : False dec} → P → X
  contradict {pr = pr} = ⊥-elim ∘ toWitnessFalse pr

open _⁇ ⦃ ... ⦄ public

¿_¿ : ∀ (X : Set ℓ) → ⦃ X ⁇ ⦄ → Dec X
¿ _ ¿ = dec

_⁇¹ : ∀ {A : Set ℓ} → (P : Pred A ℓ′) → Set (ℓ ⊔ₗ ℓ′)
P ⁇¹ = ∀ {x} → P x ⁇

dec¹ : ∀ {A : Set ℓ} {P : Pred A ℓ′} → ⦃ P ⁇¹ ⦄ → Decidable¹ P
dec¹ _ = dec

¿_¿¹ : ∀ {A : Set ℓ} (P : Pred A ℓ′) → ⦃ P ⁇¹ ⦄ → Decidable¹ P
¿ _ ¿¹ = dec¹

_⁇² : ∀ {A B : Set ℓ} → (P : REL A B ℓ′) → Set (ℓ ⊔ₗ ℓ′)
_~_ ⁇² = ∀ {x y} → (x ~ y) ⁇

dec² : ∀ {A B : Set ℓ} {_~_ : REL A B ℓ′} → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
dec² _ _ = dec

¿_¿² : ∀ {A B : Set ℓ} (_~_ : REL A B ℓ′) → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
¿ _ ¿² = dec²

_⁇³ : ∀ {A B C : Set ℓ} → (P : 3REL A B C ℓ′) → Set (ℓ ⊔ₗ ℓ′)
_~_~_ ⁇³ = ∀ {x y z} → (x ~ y ~ z) ⁇

dec³ : ∀ {A B C : Set ℓ} {_~_~_ : 3REL A B C ℓ′} → ⦃ _~_~_ ⁇³ ⦄ → Decidable³ _~_~_
dec³ _ _ _ = dec

¿_¿³ : ∀ {A B C : Set ℓ} (_~_~_ : 3REL A B C ℓ′) → ⦃ _~_~_ ⁇³ ⦄ → Decidable³ _~_~_
¿ _ ¿³ = dec³

infix -100 auto∶_
auto∶_ : ∀ (X : Set ℓ) → ⦃ X ⁇ ⦄ → Set
auto∶_ A = True ¿ A ¿

-- ** basic instances

private variable A : Set ℓ; B : Set ℓ′
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
