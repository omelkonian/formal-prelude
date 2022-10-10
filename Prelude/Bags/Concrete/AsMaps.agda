open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Semigroup

module Prelude.Bags.Concrete.AsMaps {A : Set} ⦃ _ : DecEq A ⦄ where

open import Prelude.Maps.Concrete {K = A} {V = ℕ} as Map public
  using
  ( ∅; _∪_; _⁉_
  )
  renaming
  ( Map to Bag
  ; DecEq-Map to DecEq-Bag
  ; _∈ᵈ_ to _∈ˢ_; _∉ᵈ_ to _∉ˢ_
  ; ∈ᵈ-∪⁺ˡ to ∈ˢ-∪⁺ˡ
  ; ∈ᵈ-∪⁺ʳ to ∈ˢ-∪⁺ʳ
  )

singleton : A → Bag
singleton x = Map.singleton (x , 1)
