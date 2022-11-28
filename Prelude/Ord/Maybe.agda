module Prelude.Ord.Maybe where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable
open import Prelude.Lift

open import Prelude.Orders
open import Prelude.Ord.Core

private variable X : Type ℓ

instance
  Ord-Maybe : ⦃ Ord X ⦄ → Ord (Maybe X)
  Ord-Maybe {X = X} = record {_≤_ = _≤ᵐ_; _<_ = _<ᵐ_}
    where
      _≤ᵐ_ _<ᵐ_ : Rel (Maybe X) _
      nothing ≤ᵐ _       = ↑ℓ ⊤
      just _  ≤ᵐ nothing = ↑ℓ ⊥
      just v  ≤ᵐ just v′ = v ≤ v′

      -- m <ᵐ m′ = (m ≤ᵐ m′) × (m ≢ m′)
      nothing <ᵐ nothing = ↑ℓ ⊥
      nothing <ᵐ just _  = ↑ℓ ⊤
      just _  <ᵐ nothing = ↑ℓ ⊥
      just v  <ᵐ just v′ = v < v′

-- T0D0: cannot declare these as instances without breaking instance resolution.
module Maybe-DecOrd where
  DecOrd-Maybe : ⦃ _ : Ord X ⦄ → ⦃ _ : _≤_ {A = X} ⁇² ⦄ → _≤_ {A = Maybe X} ⁇²
  DecOrd-Maybe              {x = nothing} {_}       .dec = yes it
  DecOrd-Maybe              {x = just _}  {nothing} .dec = no λ ()
  DecOrd-Maybe ⦃ _ ⦄ ⦃ ≤? ⦄ {x = just _}  {just _}  .dec = dec ⦃ ≤? ⦄

  _≤?ᵐ_ : ⦃ _ : Ord X ⦄ → ⦃ _ : _≤_ {A = X} ⁇² ⦄ → Decidable² (_≤_ {A = Maybe X})
  x ≤?ᵐ y = DecOrd-Maybe {x = x} {y} .dec

  DecStrictOrd-Maybe : ⦃ _ : Ord X ⦄ → ⦃ _ : _<_ {A = X} ⁇² ⦄ → _<_ {A = Maybe X} ⁇²
  DecStrictOrd-Maybe              {x = nothing} {nothing} .dec = no λ ()
  DecStrictOrd-Maybe              {x = nothing} {just _}  .dec = yes it
  DecStrictOrd-Maybe              {x = just _}  {nothing} .dec = no λ ()
  DecStrictOrd-Maybe ⦃ _ ⦄ ⦃ <? ⦄ {x = just _}  {just _}  .dec = dec ⦃ <? ⦄

  _<?ᵐ_ : ⦃ _ : Ord X ⦄ → ⦃ _ : _<_ {A = X} ⁇² ⦄ → Decidable² (_<_ {A = Maybe X})
  x <?ᵐ y = DecStrictOrd-Maybe {x = x} {y} .dec
