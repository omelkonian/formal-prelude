{-# OPTIONS --safe #-}
module Prelude.ToN where

open import Prelude.Init; open SetAsType

record Toℕ (A : Type ℓ) : Type ℓ where
  field toℕ : A → ℕ
open Toℕ ⦃...⦄ public

instance
  Toℕ-ℕ    = Toℕ ℕ      ∋ λ where .toℕ → id
  Toℕ-Char = Toℕ Char   ∋ λ where .toℕ → Ch.toℕ
  Toℕ-Word = Toℕ Word64 ∋ λ where .toℕ → Word.toℕ
  Toℕ-Meta = Toℕ Meta   ∋ λ where .toℕ → Meta.Meta.toℕ
    where open Meta
  Toℕ-Fin : ∀ {n} → Toℕ (Fin n)
  Toℕ-Fin .toℕ = F.toℕ
