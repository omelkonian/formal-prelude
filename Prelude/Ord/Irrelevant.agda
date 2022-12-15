{-# OPTIONS --safe #-}
module Prelude.Ord.Irrelevant where

open import Prelude.Init; open SetAsType
open import Prelude.Irrelevance.Core

open import Prelude.Ord.Core
open import Prelude.Ord.Dec

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

record Ord⁺⁺ (A : Type ℓ) : Type (lsuc ℓ) where
  field ⦃ Ord-A     ⦄ : Ord A
        ⦃ OrdLaws-A ⦄ : OrdLaws A
        ⦃ DecOrd-A  ⦄ : DecOrd A
        ⦃ ·Ord-A    ⦄ : ·Ord A
-- instance
mkOrd⁺⁺ : ∀ {A : Type ℓ} ⦃ _ : Ord A ⦄
        → ⦃ _ : OrdLaws A ⦄ ⦃ _ : DecOrd A  ⦄ ⦃ _ : ·Ord A ⦄
        → Ord⁺⁺ A
mkOrd⁺⁺ = record {}
open Ord⁺⁺ ⦃...⦄ public
