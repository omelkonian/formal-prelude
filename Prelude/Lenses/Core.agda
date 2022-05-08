open import Prelude.Init
open SetAsType

module Prelude.Lenses.Core (A : Type ℓ) (B : Type ℓ′) where

private ℓ↑ = ℓ ⊔ₗ ℓ′

Getter : Type _
Getter = A → B

Setter : Type _
Setter = A → B → A

Modifier : Type _
Modifier = A → Op₁ B → A
  -- ** dependently-typed variant
  -- (a : A)
  -- → (f : (b : B) → b ≡ a .get → B)
  -- → Σ (a′ : A). a′ .get ≡ f (a .get) refl

record Lens : Type ℓ↑ where
  field get : Getter
        set : Setter

  modify : Modifier
  modify s f = s .set $ f (s .get)

  _∙modify = modify

record Lens-Laws (l : Lens) : Type ℓ↑ where
  open Lens l
  field
    get∘set : ∀ a b → get (set a b) ≡ b
    set∘get : ∀ a → set a (get a) ≡ a
    set∘set : ∀ a b₁ b₂ → set (set a b₁) b₂ ≡ set a b₂

record Lawful-Lens : Type ℓ↑ where
  field
    lens : Lens
    laws : Lens-Laws lens
  open Lens lens
  open Lens-Laws laws

open Lens public
open Lens-Laws public
open Lawful-Lens public
