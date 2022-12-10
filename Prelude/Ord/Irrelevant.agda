module Prelude.Ord.Irrelevant where

open import Prelude.Init; open SetAsType
open import Prelude.Irrelevance

open import Prelude.Ord.Core

private variable A : Type ℓ

record ·Ord (A : Type ℓ) ⦃ _ : Ord A ⦄ : Type ℓ where
  field ⦃ ·-≤ ⦄ : ·² _≤_
        ⦃ ·-< ⦄ : ·² _<_

  ∀≡≤ = Irrelevant² _≤_ ∋ ∀≡
  ∀≡< = Irrelevant² _<_ ∋ ∀≡
-- instance
mk·Ord : ⦃ _ : Ord A ⦄ ⦃ _ : ·² _≤_ ⦄ ⦃ _ : ·² _<_  ⦄ → ·Ord A
mk·Ord = record {}
open ·Ord ⦃...⦄ public
