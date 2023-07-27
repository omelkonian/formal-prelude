{-# OPTIONS --safe #-}
module Prelude.ToZ where

open import Prelude.Init; open SetAsType
open import Prelude.ToN

record Toℤ (A : Type ℓ) : Type ℓ where
  field toℤ : A → ℤ
open Toℤ ⦃...⦄ public

instance
  Toℤ-ℤ = Toℤ ℤ ∋ λ where .toℤ → id

  Toℕ⇒Toℤ : ∀ {A : Type ℓ} → ⦃ Toℕ A ⦄ → Toℤ A
  Toℕ⇒Toℤ .toℤ = +_ ∘ toℕ
