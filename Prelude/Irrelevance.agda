module Prelude.Irrelevance where

open import Prelude.Init
open import Prelude.Decidable

private variable
  a b p : Level
  A : Set a
  B : A → Set b
  P : A → Set p

-- A type is squashed when all of its values are equal.
record Squashed (A : Set a) : Set a where
  field
    ∀≡ : ∀ (x y : A) → x ≡ y

  _∀≡↝_ : ∀ {P : A → Set p} → ∃ P → (x : A) → P x
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

open Squashed ⦃...⦄ public

instance
  Squashed-⊥ : Squashed ⊥
  Squashed-⊥ .∀≡ ()

  Squashed-⊤ : Squashed ⊤
  Squashed-⊤ .∀≡ tt tt = refl

  Squashed-≡ : ∀ {A : Set ℓ} {x y : A} → Squashed (x ≡ y)
  Squashed-≡ .∀≡ refl refl = refl

  Squashed-× : ∀ {A : Set ℓ} {B : Set ℓ′} →
    ⦃ Squashed A ⦄ → ⦃ Squashed B ⦄ → Squashed (A × B)
  Squashed-× .∀≡ (x , y) (x′ , y′) rewrite ∀≡ x x′ | ∀≡ y y′ = refl

-- instance
Dec-Σ : ⦃ _ : Squashed A ⦄ ⦃ _ : A ⁇ ⦄ ⦃ _ : ∀ {x} → B x ⁇ ⦄ → Σ A B ⁇
Dec-Σ .dec = dec ∃-dec λ _ → dec

-- Squashed-Unique×⊆ : Unique xs → Unique ys → Squashed (xs ⊆ ys)
-- Squashed-Unique×⊆ {xs = xs} {ys = ys} ∀xs≡ ∀ys≡ .∀≡ xs⊆ xs⊆′ = {!!}
-- -- need extensionality...

-- ** Products with erased proj₂, aka refinements.

record Σ₀ (A : Set ℓ) (P : A → Set ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
  constructor _,₀_
  field
    element   : A
    .property : P element
open Σ₀ public
infixr 4 _,₀_

infixr 2 _×₀_

_×₀_ : ∀ (A : Set ℓ) (B : Set ℓ′) → Set (ℓ ⊔ₗ ℓ′)
A ×₀ B = Σ₀ A (const B)

∃₀ : ∀ {A : Set ℓ} → (A → Set ℓ′) → Set (ℓ ⊔ₗ ℓ′)
∃₀ = Σ₀ _

{-
  record Squash {a} (A : Set a) : Set a where
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
