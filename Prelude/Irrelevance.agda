module Prelude.Irrelevance where

open import Level
open import Function
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Prelude.Decidable

open import Data.Unit
open import Relation.Binary.PropositionalEquality

private
  variable
    a b p : Level
    A : Set a
    B : A → Set b
    P : A → Set p

record Squashed (A : Set a) : Set a where
  field
    ∀≡ : ∀ (x y : A) → x ≡ y

  _∀≡↝_ : ∀ {P : A → Set p} → ∃ P → (x : A) → P x
  _∀≡↝_ (y , p) x rewrite ∀≡ y x = p
open Squashed ⦃ ... ⦄ public

instance
  Squashed-⊤ : Squashed ⊤
  Squashed-⊤ .∀≡ tt tt = refl

  Dec-Σ : ⦃ _ : Squashed A ⦄ ⦃ _ : A ⁇ ⦄ ⦃ _ : ∀ {x} → B x ⁇ ⦄ → Σ A B ⁇
  Dec-Σ .dec
    with dec
  ... | no ¬x = no $ ¬x ∘ proj₁
  ... | yes x
    with dec
  ... | no ¬Px = no $ ¬Px ∘ (_∀≡↝ x)
  ... | yes Px = yes (x , Px)

-- open import Prelude.Lists
-- private variable xs ys : List A

-- Squashed-Unique×⊆ : Unique xs → Unique ys → Squashed (xs ⊆ ys)
-- Squashed-Unique×⊆ {xs = xs} {ys = ys} ∀xs≡ ∀ys≡ .∀≡ xs⊆ xs⊆′ = {!!}
-- -- need extensionality...

-- Products with erased proj₂, aka refinements.

private variable ℓ ℓ′ : Level

record Σ₀ (A : Set ℓ) (P : A → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,₀_
  field
    element   : A
    .property : P element
open Σ₀ public
infixr 4 _,₀_

infixr 2 _×₀_

_×₀_ : ∀ (A : Set ℓ) (B : Set ℓ′) → Set (ℓ ⊔ ℓ′)
A ×₀ B = Σ₀ A (const B)

∃₀ : ∀ {A : Set ℓ} → (A → Set ℓ′) → Set (ℓ ⊔ ℓ′)
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
