module Prelude.Ord.Maybe where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Lift

open import Prelude.Ord.Core

private variable A : Type ℓ

module _ ⦃ _ : DecEq A ⦄ ⦃ _ : Ord A ⦄ where
  private
    _≤ᵐ_ _<ᵐ_ : Rel (Maybe A) _
    nothing ≤ᵐ _       = ↑ℓ ⊤
    just _  ≤ᵐ nothing = ↑ℓ ⊥
    just v  ≤ᵐ just v′ = v ≤ v′

    -- m <ᵐ m′ = (m ≤ᵐ m′) × (m ≢ m′)
    nothing <ᵐ nothing = ↑ℓ ⊥
    nothing <ᵐ just _  = ↑ℓ ⊤
    just _  <ᵐ nothing = ↑ℓ ⊥
    just v  <ᵐ just v′ = v < v′

  instance
    Dec-≤ᵐ : _≤ᵐ_ ⁇²
    Dec-≤ᵐ {nothing} {_}       .dec = yes it
    Dec-≤ᵐ {just _}  {nothing} .dec = no λ ()
    Dec-≤ᵐ {just _}  {just _}  .dec = Dec-≤ .dec

    Dec-<ᵐ : _<ᵐ_ ⁇²
    Dec-<ᵐ {nothing} {nothing} .dec = no λ ()
    Dec-<ᵐ {nothing} {just _}  .dec = yes it
    Dec-<ᵐ {just _}  {nothing} .dec = no λ ()
    Dec-<ᵐ {just _}  {just _}  .dec = Dec-< .dec

    Ord-Maybe : Ord (Maybe A)
    Ord-Maybe = record
      { _≤_ = _≤ᵐ_; _<_ = _<ᵐ_
      ; Dec-≤ = λ {x}{y} → Dec-≤ᵐ {x}{y}
      ; Dec-< = λ {x}{y} → Dec-<ᵐ {x}{y}
      }

    postulate OrdLaws-Maybe : OrdLaws (Maybe A)

  _≤?ᵐ_ = Decidable² _≤ᵐ_ ∋ _≤?_
  _<?ᵐ_ = Decidable² _<ᵐ_ ∋ _<?_
