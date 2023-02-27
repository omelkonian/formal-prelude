{-# OPTIONS --safe --with-K #-}

open import Prelude.Init; open SetAsType
open import Prelude.DecEq.Core

module Prelude.DecEq.WithK {A : Type ℓ} ⦃ _ : DecEq A ⦄ where

≟-refl : ∀ (x : A) → (x ≟ x) ≡ yes refl
≟-refl x with refl , p ← dec-yes (x ≟ x) refl = p

==-refl : ∀ (x : A) → T (x == x)
==-refl _ = subst (T ∘ isYes) (sym $ ≟-refl _) tt

instance
  DecEq-List⁺ : DecEq (List⁺ A)
  DecEq-List⁺ ._≟_ (x ∷ xs) (y ∷ ys)
    with x ≟ y
  ... | no x≢y = no λ where refl → x≢y refl
  ... | yes refl
    with xs ≟ ys
  ... | no xs≢ys = no λ where refl → xs≢ys refl
  ... | yes refl = yes refl

  DecEq-Σ : ∀ {B : A → Type ℓ′} ⦃ _ : ∀ {x} → DecEq (B x) ⦄ → DecEq (Σ A B)
  DecEq-Σ ._≟_ (x , y) (x′ , y′)
    with x ≟ x′
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl
    with y ≟ y′
  ... | no ¬p    = no λ where refl → ¬p refl
  ... | yes refl = yes refl
