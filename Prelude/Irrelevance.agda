module Prelude.Irrelevance where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable
open import Prelude.General

private variable
  A : Type ℓ
  B : A → Type ℓ′

-- A type is squashed when all of its values are equal.
record ·_ (A : Type ℓ) : Type ℓ where
  field ∀≡ : Irrelevant A

  _∀≡↝_ : ∃ B → (x : A) → B x
  _∀≡↝_ (y , p) x rewrite ∀≡ y x = p

  -- A dependent product indexed by a squashed type is decidable!
  -- T0D0: generalize to enumerable indices
  _∃-dec_ : Dec A → (∀ a → Dec (B a)) → Dec (Product.Σ A B)
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

  ·-≡ : ∀ {A : Type ℓ} {x y : A} → · (x ≡ y)
  ·-≡ .∀≡ refl refl = refl

  ·-× : ∀ {A : Type ℓ} {B : Type ℓ′} →
    ⦃ · A ⦄ → ⦃ · B ⦄ → · (A × B)
  ·-× .∀≡ (x , y) (x′ , y′) rewrite ∀≡ x x′ | ∀≡ y y′ = refl

-- instance
Dec-Σ : ⦃ _ : · A ⦄ ⦃ _ : A ⁇ ⦄ ⦃ _ : ∀ {x} → B x ⁇ ⦄ → Σ A B ⁇
Dec-Σ .dec = dec ∃-dec λ _ → dec

-- ·-Unique×⊆ : Unique xs → Unique ys → · (xs ⊆ ys)
-- ·-Unique×⊆ {xs = xs} {ys = ys} ∀xs≡ ∀ys≡ .∀≡ xs⊆ xs⊆′ = {!!}
-- -- need extensionality...

-- ** Products with erased proj₂, aka refinements.

record Σ₀ (A : Type ℓ) (P : A → Type ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  constructor _,₀_
  field
    element   : A
    .property : P element
open Σ₀ public
infixr 4 _,₀_

infixr 2 _×₀_

_×₀_ : ∀ (A : Type ℓ) (B : Type ℓ′) → Type (ℓ ⊔ₗ ℓ′)
A ×₀ B = Σ₀ A (const B)

∃₀ : ∀ {A : Type ℓ} → (A → Type ℓ′) → Type (ℓ ⊔ₗ ℓ′)
∃₀ = Σ₀ _

{-
  record Squash {a} (A : Type a) : Type a where
    constructor squash
    field
      .unsquash : A
  open Squash public

  ¬squash : .(¬ A) → ¬ Squash A
  ¬squash ¬x (squash x) = {!¬x x!}

  instance
    Dec-Squash : ⦃ _ : A ⁇ ⦄ → Squash A ⁇
    Dec-Squash .dec
      with dec
    ... | no ¬p = no (¬squash ¬p)
    ... | yes p = yes (squash p)

    Dec-Σ : ∀ ⦃ _ : A ⁇ ⦄ ⦃ _ : ∀ {x} → B x ⁇ ⦄ → Σ (Squash A) B ⁇
    Dec-Σ .dec
      with dec
    ... | no ¬x = no (¬x ∘ proj₁)
    ... | yes x
      with dec
    ... | no ¬Xx = no λ{ (squash _ , Xx) → ¬Xx Xx }
    ... | yes Xx = yes (x , Xx)
-}

-- ** irrelevant bottom type

module _ {ℓ : Level} where
  private data ∅ : Type ℓ where
  record ·⊥ : Type ℓ where
    field .absurd : ∅

  infix 3 ·¬_
  ·¬_ : Type ℓ → Type ℓ
  ·¬_ A = A → ·⊥

  instance
    ·-·¬ : · (·¬ A)
    ·-·¬ .∀≡ _ _ = refl

  ·⊥-elim : ·⊥ → A
  ·⊥-elim ()

  ·⊥⇒⊥ : ·¬ A → ¬ A
  ·⊥⇒⊥ ¬p = ·⊥-elim ∘ ¬p

  ⊥⇒·⊥ : ¬ A → ·¬ A
  ⊥⇒·⊥ ¬p = ⊥-elim ∘ ¬p

  ·⊥⇔⊥ : ·¬ A ↔ ¬ A
  ·⊥⇔⊥ = ·⊥⇒⊥ , ⊥⇒·⊥
