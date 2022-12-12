module Prelude.Ord.Maybe where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Lift
open import Prelude.Irrelevance.Core

open import Prelude.Ord.Core
open import Prelude.Ord.Dec
open import Prelude.Ord.Irrelevant

module _ {A : Type ℓ} ⦃ _ : Ord A ⦄ where
  instance
    Ord-Maybe : Ord (Maybe A)
    Ord-Maybe = λ where
      ._≤_ → λ where
        nothing  _         → ↑ℓ ⊤
        (just _) nothing   → ↑ℓ ⊥
        (just v) (just v′) → v ≤ v′
      ._<_ → λ where
        nothing  nothing   → ↑ℓ ⊥
        nothing  (just _)  → ↑ℓ ⊤
        (just _) nothing   → ↑ℓ ⊥
        (just v) (just v′) → v < v′

  module _ ⦃ _ : DecOrd A ⦄ where
    instance
      Dec-≤ᵐ : _≤_ {A = Maybe A} ⁇²
      Dec-≤ᵐ {nothing} {_}       .dec = yes it
      Dec-≤ᵐ {just _}  {nothing} .dec = no λ ()
      Dec-≤ᵐ {just x}  {just y}  .dec = x ≤? y

      Dec-<ᵐ : _<_ {A = Maybe A} ⁇²
      Dec-<ᵐ {nothing} {nothing} .dec = no λ ()
      Dec-<ᵐ {nothing} {just _}  .dec = yes it
      Dec-<ᵐ {just _}  {nothing} .dec = no λ ()
      Dec-<ᵐ {just x}  {just y}  .dec = x <? y

      DecOrd-Maybe : DecOrd (Maybe A)
      DecOrd-Maybe = λ where
        .Dec-≤ {x} → Dec-≤ᵐ {x}
        .Dec-< {x} → Dec-<ᵐ {x}

    _≤?ᵐ_ = Decidable² (_≤_ {A = Maybe A}) ∋ _≤?_
    _<?ᵐ_ = Decidable² (_<_ {A = Maybe A}) ∋ _<?_

  module _ ⦃ _ : OrdLaws A ⦄ where instance
    postulate OrdLaws-Maybe : OrdLaws (Maybe A)

  module _ ⦃ _ : ·Ord A ⦄ where instance
    ·Ord-Maybe : ·Ord (Maybe A)
    ·Ord-Maybe = λ where
      .·-≤ {just x}  {just y}  .∀≡ p q → ∀≡ p q
      .·-≤ {nothing} {just _}  .∀≡ _ _ → refl
      .·-≤ {nothing} {nothing} .∀≡ _ _ → refl

      .·-< {just x}  {just y} .∀≡ p q → ∀≡ p q
      .·-< {nothing} {just _} .∀≡ _ _ → refl

module _ {A : Type ℓ} ⦃ _ : Ord⁺⁺ A ⦄ where instance
  Ord⁺⁺-Maybe : Ord⁺⁺ (Maybe A)
  Ord⁺⁺-Maybe = mkOrd⁺⁺
