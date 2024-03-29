{-# OPTIONS --safe #-}
module Prelude.Ord.Dec where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable
open import Prelude.DecEq.Core

open import Prelude.Ord.Core

private variable A : Type ℓ

record DecOrd (A : Type ℓ) ⦃ _ : Ord  A ⦄ : Type ℓ where
  field ⦃ Dec-≤ ⦄ : _≤_ ⁇²
        ⦃ Dec-< ⦄ : _<_ ⁇²

  infix 4 _≤?_ _≤ᵇ_ _≰?_ _≰ᵇ_ _≥?_ _≥ᵇ_ _≱?_ _≱ᵇ_
          _<?_ _<ᵇ_ _≮?_ _≮ᵇ_ _>?_ _>ᵇ_ _≯?_ _≯ᵇ_
  _≤?_ = Decidable² _≤_ ∋ dec²; _≤ᵇ_ = isYes ∘₂ _≤?_
  _≰?_ = ¬? ∘₂ _≤?_; _≰ᵇ_ = isYes ∘₂ _≰?_
  _≥?_ = flip _≤?_; _≥ᵇ_ = isYes ∘₂ _≥?_
  _≱?_ = ¬? ∘₂ _≥?_; _≱ᵇ_ = isYes ∘₂ _≱?_
  _<?_ = Decidable² _<_ ∋ dec²; _<ᵇ_ = isYes ∘₂ _<?_
  _≮?_ = ¬? ∘₂ _<?_; _≮ᵇ_ = isYes ∘₂ _≮?_
  _>?_ = flip _<?_; _>ᵇ_ = isYes ∘₂ _>?_
  _≯?_ = ¬? ∘₂ _>?_; _≯ᵇ_ = isYes ∘₂ _≯?_

  module _ ⦃ _ : DecEq A ⦄ ⦃ _ : OrdLaws A ⦄ where

    open Binary

    isDecStrictPartialOrder = IsDecStrictPartialOrder _<_ ∋ record
      { _≟_ = _≟_
      ; _<?_ = _<?_
      ; isStrictPartialOrder = isStrictPartialOrder }

    isDecTotalOrder = IsDecTotalOrder _≤_ ∋ record
      { _≟_ = _≟_
      ; _≤?_ = _≤?_
      ; isTotalOrder = isTotalOrder }

-- instance
mkDecOrd : ⦃ _ : Ord A ⦄ ⦃ _ : _≤_ ⁇² ⦄ ⦃ _ : _<_ ⁇² ⦄ → DecOrd A
mkDecOrd = record {}
open DecOrd ⦃...⦄ public

module _ {A : Type ℓ} {_<_ : Rel A ℓ} ⦃ _ : DecEq A ⦄ (_<?_ : Decidable² _<_) where
  ≤?-from-<? : Decidable² (≤-from-< _<_)
  ≤?-from-<? x y = (x ≟ y) ⊎-dec (x <? y)

  instance _ = mkOrd< _<_

  mkDecOrd< : DecOrd A
  mkDecOrd< .Dec-< .dec = _ <? _
  mkDecOrd< .Dec-≤ .dec = ≤?-from-<? _ _
