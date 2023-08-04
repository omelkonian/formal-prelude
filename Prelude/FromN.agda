{-# OPTIONS --safe #-}
module Prelude.FromN where

open import Prelude.Init; open SetAsType
open import Prelude.Newtype

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

  Fromℕ-ℕᵇ : Fromℕ ℕᵇ
  Fromℕ-ℕᵇ .fromℕ = Nat.Bin.fromℕ

  Fromℕ-newtype : ∀ {A : Type ℓ} → ⦃ Fromℕ A ⦄ → Fromℕ (newtype A)
  Fromℕ-newtype .fromℕ = mk ∘ fromℕ
