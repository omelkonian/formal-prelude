-- 1) ≡reasoning-like syntax, but to manipulate terms of different types, rather than equality.
-- 2) generic ≡reasoning that uses typeclasses to automatically pick the suitable relation

module Prelude.Tactics.TermReasoning where

open import Prelude.Init

record Relatable {a ℓ : Level} (A : Set a) (_∼_ : Rel A ℓ) : Set (a ⊔ₗ ℓ) where
  field ~-trans : Transitive _∼_

  infix 4 _IsRelatedTo_
  data _IsRelatedTo_ : A → A → Set (a ⊔ₗ ℓ) where
    singleStep : ∀ x → x IsRelatedTo x
    multiStep  : ∀ {x y} (x∼y : x ∼ y) → x IsRelatedTo y
  data IsMultiStep {x y} : x IsRelatedTo y → Set (a ⊔ₗ ℓ) where
    isMultiStep : ∀ x∼y → IsMultiStep (multiStep x∼y)

  IsMultiStep? : ∀ {x y} (x∼y : x IsRelatedTo y) → Dec (IsMultiStep x∼y)
  IsMultiStep? (multiStep x<y) = yes (isMultiStep x<y)
  IsMultiStep? (singleStep _)  = no λ()

  infix  1 begin_
  infixr 2 step-∼ step-≡ step-≡˘
  infixr 2 _≡⟨⟩_
  infix  3 _∎

  -- Beginning of a proof

  begin_ : ∀ {x y} (x∼y : x IsRelatedTo y) → {True (IsMultiStep? x∼y)} → x ∼ y
  begin (multiStep x∼y) = x∼y

  -- Standard step with the relation

  step-∼ : ∀ x {y z} → y IsRelatedTo z → x ∼ y → x IsRelatedTo z
  step-∼ _ (singleStep _) x∼y  = multiStep x∼y
  step-∼ _ (multiStep y∼z) x∼y = multiStep (~-trans x∼y y∼z)

  -- Step with a non-trivial propositional equality

  step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
  step-≡ _ x∼z refl = x∼z

  -- Step with a flipped non-trivial propositional equality

  step-≡˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
  step-≡˘ _ x∼z refl = x∼z

  -- -- Step with a trivial propositional equality

  _≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
  _ ≡⟨⟩ x∼y = x∼y

  -- Termination

  _∎ : ∀ x → x IsRelatedTo x
  _∎ = singleStep

  -- Syntax declarations

  syntax step-∼  x y∼z x∼y = x ∼⟨  x∼y ⟩ y∼z
  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
