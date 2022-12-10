module Prelude.Ord where

open import Prelude.Ord.Core public
open import Prelude.Ord.Dec public
open import Prelude.Ord.Irrelevant public

open import Prelude.Init; open SetAsType
record Ord⁺⁺ (A : Type ℓ) : Type (lsuc ℓ) where
  field ⦃ Ord-A     ⦄ : Ord A
        ⦃ OrdLaws-A ⦄ : OrdLaws A
        ⦃ DecOrd-A  ⦄ : DecOrd A
        ⦃ ·Ord-A    ⦄ : ·Ord A
instance
  mkOrd⁺⁺ : ∀ {A : Type ℓ} ⦃ _ : Ord A ⦄
          → ⦃ _ : OrdLaws A ⦄ ⦃ _ : DecOrd A  ⦄ ⦃ _ : ·Ord A ⦄
          → Ord⁺⁺ A
  mkOrd⁺⁺ = record {}
open Ord⁺⁺ ⦃...⦄ public

open import Prelude.Ord.MinMax public
open import Prelude.Ord.Sort public
open import Prelude.Ord.Iso public

open import Prelude.Ord.Instances public
open import Prelude.Ord.List public
-- T0D0: cannot export these without breaking instance resolution
open import Prelude.Ord.Product -- public
open import Prelude.Ord.Maybe   -- public

open import Prelude.Ord.Derive public
