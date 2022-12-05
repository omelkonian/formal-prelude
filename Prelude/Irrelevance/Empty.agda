module Prelude.Irrelevance.Empty where

open import Prelude.Init; open SetAsType
open import Prelude.General

open import Prelude.Irrelevance.Core

private variable A : Type ℓ

module _ {ℓ : Level} where
  private data ∅ : Type ℓ where
  record ·⊥ : Type ℓ where
    field .absurd : ∅

  ·⊥-elim : ·⊥ → A
  ·⊥-elim ()

  ·⊥⇒⊥ = (·⊥ → ⊥) ∋ ·⊥-elim
  ⊥⇒·⊥ = (⊥ → ·⊥) ∋ ⊥-elim
  ·⊥⇔⊥ = (·⊥ ↔ ⊥) ∋ ·⊥⇒⊥ , ⊥⇒·⊥

  infix 3 ·¬_
  ·¬_ : Type ℓ → Type ℓ
  ·¬_ A = A → ·⊥

  instance
    ·-·¬ : · (·¬ A)
    ·-·¬ .∀≡ _ _ = refl

  ·¬⇒¬ : ·¬ A → ¬ A
  ·¬⇒¬ ¬p = ·⊥-elim ∘ ¬p

  ¬⇒·¬ : ¬ A → ·¬ A
  ¬⇒·¬ ¬p = ⊥-elim ∘ ¬p

  ·¬⇔¬ : ·¬ A ↔ ¬ A
  ·¬⇔¬ = ·¬⇒¬ , ¬⇒·¬

infix 4 _·≢_
_·≢_ : Rel A _
x ·≢ y = ·¬ x ≡ y
