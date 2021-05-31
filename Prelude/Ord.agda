module Prelude.Ord where

open import Prelude.Init hiding (_≤_; _≤?_; _≥_; _≥?_)
open import Prelude.Lists

record Ord (A : Set ℓ) : Set (lsuc ℓ) where
  field
    _≤_ : Rel₀ A

  _≥_ : Rel₀ A
  y ≥ x = x ≤ y

open Ord ⦃ ... ⦄ public

record DecOrd (A : Set ℓ) : Set (lsuc ℓ) where
  field
    overlap ⦃ super ⦄ : Ord A
    _≤?_ : Decidable² _≤_

  _≥?_ : Decidable² _≥_
  y ≥? x = x ≤? y

  min max : Op₂ A
  min x y = if ⌊ x ≤? y ⌋ then x else y
  max x y = min y x

  minimum maximum : A → List A → A
  minimum = foldl min
  maximum = foldl max

  minimum⁺ maximum⁺ : List⁺ A → A
  minimum⁺ (x ∷ xs) = minimum x xs
  maximum⁺ (x ∷ xs) = maximum x xs

open DecOrd ⦃ ... ⦄ public

instance
  Ord-ℕ : Ord ℕ
  Ord-ℕ ._≤_ = Nat._≤_
  -- Ord-ℕ ._<_ = Nat._<_

  DecOrd-ℕ : DecOrd ℕ
  DecOrd.super DecOrd-ℕ = it
  DecOrd-ℕ ._≤?_ = Nat._≤?_

postulate
  ∀≤max⁺ : ∀ (ts : List⁺ ℕ) → All⁺ (_≤ maximum⁺ ts) ts
  ∀≤max : ∀ t₀ (ts : List ℕ) → All (_≤ maximum t₀ ts) ts
