{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open Binary
open import Prelude.General
open import Prelude.Lift
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Irrelevance

open import Prelude.Ord.Core
open import Prelude.Ord.Dec
open import Prelude.Ord.Irrelevant

module Prelude.Ord.These where

-- unquoteDecl Ord-These DecOrd-These OrdLaws-These =
--   DERIVE Ord [ quote These , Ord-These , DecOrd-These , OrdLaws-These ]

module _ {A : Type ℓ} {B : Type ℓ′} ⦃ _ : Ord A ⦄ ⦃ _ : Ord B ⦄ where
  instance
    Ord-These : Ord (These A B)
    Ord-These = mkOrd< λ where
      (this x) (this y) → ↑ℓ (x < y) {ℓ ⊔ₗ ℓ′}
      (this _) (that _) → ↑ℓ ⊤
      (this _) (these _ _) → ↑ℓ ⊤
      (that _) (this _) → ↑ℓ ⊥
      (that x) (that y) → ↑ℓ (x < y) {ℓ ⊔ₗ ℓ′}
      (that _) (these _ _) → ↑ℓ ⊤
      (these _ _) (this _) → ↑ℓ ⊥
      (these _ _) (that _) → ↑ℓ ⊥
      (these x y) (these x′ y′) → (x < x′) ⊎ ((x ≡ x′) × (y < y′))

  module _ ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : DecOrd A ⦄ ⦃ _ : DecOrd B ⦄ where
    _<?-These_ : Decidable² (_<_ {A = These A B})
    _<?-These_ = λ where
      (this x) (this y) → ↑ℓ-dec (x <? y)
      (this _) (that _) → yes it
      (this _) (these _ _) → yes it
      (that _) (this _) → no λ ()
      (that x) (that y) → ↑ℓ-dec (x <? y)
      (that _) (these _ _) → yes it
      (these _ _) (this _) → no λ ()
      (these _ _) (that _) → no λ ()
      (these x y) (these x′ y′) → (x <? x′) ⊎-dec ((x ≟ x′) ×-dec (y <? y′))

    instance
      Dec-<These : _<_ {A = These A B} ⁇²
      Dec-<These .dec = _ <?-These _

      DecOrd-These : DecOrd (These A B)
      DecOrd-These = record {}

  module _ ⦃ _ : OrdLaws A ⦄ ⦃ _ : OrdLaws B ⦄ where postulate instance
    OrdLaws-These : OrdLaws (These A B)
  module _ ⦃ _ : ·Ord A ⦄ ⦃ _ : ·Ord B ⦄ where postulate instance
    ·Ord-These : ·Ord (These A B)

module _ {A : Type ℓ} {B : Type ℓ′} ⦃ _ : Ord⁺⁺ A ⦄ ⦃ _ : Ord⁺⁺ B ⦄ where instance
  Ord⁺⁺-These : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → Ord⁺⁺ (These A B)
  Ord⁺⁺-These = mkOrd⁺⁺
