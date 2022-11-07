------------------------------------------------------------------------
-- Numerical sums.

module Prelude.Lists.Sums where

open import Prelude.Init
open Nat using (_≤_; _≤?_; _≥_)
open import Prelude.Bifunctor

private variable
  n : ℕ
  ns : List ℕ
  X : Pred₀ ℕ
  Y : Pred₀ ℕ

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

postulate
  ∑₁-limit : ∀ {lim} {xs : List (∃ X)} {k₁ : ∀ {n} → lim ≤ n → X n → Y lim} {k₂ : ∀ {n} → n ≤ lim → X n → Y n}
    → ∑₁ xs ≥ lim
    → ∑₁ (limit lim k₁ k₂ xs) ≥ lim

  ∑₁-++ : ∀ {xs ys : List (∃ X)}
    → ∑₁ (xs ++ ys)
    ≡ ∑₁ xs + ∑₁ ys

  ∑ℕ-∀≡0 : ∀ {xs}
    → All (_≡ 0) xs
    → ∑ℕ xs ≡ 0

  ∑ℕ-⊆ : ∀ {xs ys} → xs ⊆ ys → ∑ℕ xs ≤ ∑ℕ ys

  ∑₁-map₂ : ∀ {xs : List (∃ X)} {f : ∀ {n} → X n → Y n}
    → ∑₁ (map (map₂′ f) xs)
    ≡ ∑₁ xs

  ∑₁-single : ∀ {x : ∃ X} → ∑₁ [ n , x ] ≡ n

  x∈∑ℕ : n L.Mem.∈ ns → n ≤ ∑ℕ ns
