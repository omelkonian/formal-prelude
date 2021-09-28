module Prelude.FromN where

open import Prelude.Init

record Fromℕ (A : Set ℓ) : Set ℓ where
  field fromℕ : ℕ → A
open Fromℕ ⦃...⦄ public

instance
  Fromℕ-ℕ : Fromℕ ℕ
  Fromℕ-ℕ .fromℕ = id

  Fromℕ-Char : Fromℕ Char
  Fromℕ-Char .fromℕ = Ch.fromℕ

  Fromℕ-Fin : Fromℕ (∃ Fin)
  Fromℕ-Fin .fromℕ = -,_ ∘ F.fromℕ

  Fromℕ-Word : Fromℕ Word64
  Fromℕ-Word .fromℕ = Word.fromℕ
