module Prelude.Irrelevance.Empty where

import Relation.Nullary.Decidable as Dec

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Decidable

open import Prelude.Irrelevance.Core

private variable A : Type ℓ

private data ∅ : Type where
record ·⊥ : Type where
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

·T : Pred₀ Bool
·T true  = ⊤
·T false = ·⊥

infix 4 _·≢_
_·≢_ : Rel A _
x ·≢ y = ·¬ x ≡ y

-- ** decidability

·¬? : Dec A → Dec (·¬ A)
·¬? = Dec.map′ ¬⇒·¬ ·¬⇒¬ ∘ ¬?

instance
  Dec-·⊥ : ·⊥ ⁇
  Dec-·⊥ .dec = no λ()
