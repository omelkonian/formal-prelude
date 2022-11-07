open import Prelude.Init; open SetAsType
open import Prelude.DecEq

module Prelude.Bags where

open import
  -- ** pick implementation to export
  -- Prelude.Bags.AsMaps
  -- Prelude.Bags.AsPartialFunctions
  Prelude.Bags.AsLists
  public

Bag⟨_⟩ : (A : Type) ⦃ _ : DecEq A ⦄ → Type
Bag⟨ A ⟩ = Bag {A = A}
