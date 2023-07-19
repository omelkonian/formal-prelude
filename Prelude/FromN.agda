{-# OPTIONS --safe #-}
module Prelude.FromN where

open import Prelude.Init; open SetAsType

record Fromℕ (A : Type ℓ) : Type ℓ where
  field fromℕ : ℕ → A
open Fromℕ ⦃...⦄ public

instance
  Fromℕ-ℕ : Fromℕ ℕ
  Fromℕ-ℕ .fromℕ = id

  Fromℕ-Int : Fromℕ ℤ
  Fromℕ-Int .fromℕ = +_

  Fromℕ-Char : Fromℕ Char
  Fromℕ-Char .fromℕ = Ch.fromℕ

  Fromℕ-Fin : Fromℕ (∃ Fin)
  Fromℕ-Fin .fromℕ = -,_ ∘ F.fromℕ

  Fromℕ-Word : Fromℕ Word64
  Fromℕ-Word .fromℕ = Word.fromℕ
