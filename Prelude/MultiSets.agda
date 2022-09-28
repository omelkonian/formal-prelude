open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Semigroup

module Prelude.MultiSets {A : Set} where

open import Prelude.Maps {K = A} {V = ℕ}
  using
  (∅; _∪_; _⁉_)
  renaming
  ( Map to MultiSet
  ; _∈ᵈ_ to _∈ˢ_; _∉ᵈ_ to _∉ˢ_
  ; _♯ᵐ_ to _♯ˢ_
  )
