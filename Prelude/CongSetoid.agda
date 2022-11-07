module Prelude.CongSetoid where

open import Prelude.Init; open SetAsType
open import Prelude.Setoid

-- ** homogeneous version
record CongSetoid (A : Type ℓ) ⦃ _ : ISetoid A ⦄ ⦃ _ : Setoid-Laws A ⦄ : Typeω where
  field ≈-cong : ∀ (f : A → A) → Congruent _≈_ _≈_ f
open CongSetoid ⦃...⦄ public

-- ** heterogeneous version
record CongSetoid′ (A : Type ℓ) ⦃ _ : ISetoid A ⦄ ⦃ _ : Setoid-Laws A ⦄ : Typeω where
  field ≈-cong′ : ∀ {B : Type ℓ′} ⦃ _ : ISetoid B ⦄ ⦃ _ : Setoid-Laws B ⦄ →
                  ∀ (f : A → B) → Congruent _≈_ _≈_ f
open CongSetoid′ ⦃...⦄ public
