{-# OPTIONS --safe #-}
module Prelude.Allable where

open import Prelude.Init hiding (All); open SetAsType
open import Prelude.DecEq.Core

record Allable (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field
    All : ∀ {A} → Pred₀ A → F A → Type ℓ

  syntax All P xs = ∀[∈ xs ] P
  All′ = All
  syntax All′ (λ x → P) xs = ∀[ x ∈ xs ] P

open Allable ⦃...⦄ public

instance
  Allable-List : Allable {ℓ} List
  Allable-List .All = L.All.All

private
  open import Prelude.Nary
  open import Prelude.Decidable
  open import Prelude.Ord.Core
  open import Prelude.Ord.Instances

  _ : ∀[ x ∈ ⟦ 1 ,  2 , 3 ⟧ ] (x > 0)
  _ = auto
