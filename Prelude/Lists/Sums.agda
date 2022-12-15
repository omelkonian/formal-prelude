------------------------------------------------------------------------
-- Numerical sums.

{-# OPTIONS --safe #-}
module Prelude.Lists.Sums where

open import Prelude.Init
open Nat using (_≤_; _≤?_; _≥_)
open import Prelude.Bifunctor

private variable
  n : ℕ
  ns : List ℕ
  X Y : Pred ℕ ℓ

∑ℕ : List ℕ → ℕ
∑ℕ = sum

∑⁺ : List⁺ ℕ → ℕ
∑⁺ = ∑ℕ ∘ L.NE.toList

∑₁ : List (∃ X) → ℕ
∑₁ = ∑ℕ ∘ map proj₁


limit : (lim : ℕ)
      → (∀ {n} → lim ≤ n → X n → Y lim)
      → (∀ {n} → n ≤ lim → X n → Y n)
      → List (∃ X)
      → List (∃ Y)
limit {X = X} {Y = Y} l k₁ k₂ = map f
  where
    f : ∃ X → ∃ Y
    f (n , x) with l ≤? n
    ... | yes l≤ = l , k₁ l≤ x
    ... | no ¬l≤ = n , k₂ (Nat.≰⇒≥ ¬l≤) x
