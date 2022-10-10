module Prelude.Bags.Concrete where

open import Prelude.DecEq
open import Prelude.Bags.Concrete.AsMaps public

Bag⟨_⟩ : (A : Set) ⦃ _ : DecEq A ⦄ → Set
Bag⟨ A ⟩ = Bag {A = A}
