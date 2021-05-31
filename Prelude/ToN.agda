module Prelude.ToN where

open import Prelude.Init

record Toℕ (A : Set ℓ) : Set ℓ where
  field
    toℕ : A → ℕ
open Toℕ ⦃ ... ⦄ public

instance
  Toℕ-ℕ : Toℕ ℕ
  Toℕ-ℕ .toℕ = id

  Toℕ-Char : Toℕ Char
  Toℕ-Char .toℕ = Ch.toℕ

  Toℕ-Fin : ∀ {n} → Toℕ (Fin n)
  Toℕ-Fin .toℕ = F.toℕ
