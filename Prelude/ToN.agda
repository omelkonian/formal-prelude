module Prelude.ToN where

open import Prelude.Init

record Toℕ {a} (A : Set a) : Set a where
  field
    toℕ : A → ℕ
open Toℕ {{...}} public

instance
  Toℕ-Char : Toℕ Char
  Toℕ-Char .toℕ = Ch.toℕ

  Toℕ-Fin : ∀ {n} → Toℕ (Fin n)
  Toℕ-Fin .toℕ = F.toℕ
