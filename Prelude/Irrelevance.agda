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
open Squashed {{...}} public

instance
  Squashed-⊤ : Squashed ⊤
  Squashed-⊤ .∀≡ tt tt = refl

  Dec-Σ : {{_ : Squashed A}} {{_ : A ⁇}} {{_ : ∀ {x} → B x ⁇}} → Σ A B ⁇
  Dec-Σ .dec
    with dec
  ... | no ¬x = no (¬x ∘ proj₁)
  ... | yes x
    with dec
  ... | no ¬Px = no (¬Px ∘ (_∀≡↝ x))
  ... | yes Px = yes (x , Px)


{-
record Squash {a} (A : Set a) : Set a where
  constructor squash
  field
    .unsquash : A
open Squash public

¬squash : .(¬ A) → ¬ Squash A
¬squash ¬x (squash x) = {!¬x x!}

instance
  Dec-Squash : {{_ : A ⁇}} → Squash A ⁇
  Dec-Squash .dec
    with dec
  ... | no ¬p = no (¬squash ¬p)
  ... | yes p = yes (squash p)

  Dec-Σ : ∀ {{_ : A ⁇}} {{_ : ∀ {x} → B x ⁇}} → Σ (Squash A) B ⁇
  Dec-Σ .dec
    with dec
  ... | no ¬x = no (¬x ∘ proj₁)
  ... | yes x
    with dec
  ... | no ¬Xx = no λ{ (squash _ , Xx) → ¬Xx Xx }
  ... | yes Xx = yes (x , Xx)
-}
