module Prelude.Bags.Example where

open import Prelude.Init
open import Prelude.DecEq

private
  module ConcreteExample where
    open import Prelude.Bags

    _ = Bag⟨ String ⟩ ∋ singleton "sth" ∪ singleton "sth"
    _ = DecEq Bag⟨ String ⟩ ∋ it

    _ : "sth" ∈ˢ (singleton "else" ∪ singleton "sth" ∪ singleton "else")
    _ = here refl -- ✓ COMPUTES, AS EXPECTED!

  module AbstractExample where
    open import Prelude.Bags.Abstract

    -- _ : "sth" ∈ˢ (singleton "else" ∪ singleton "sth" ∪ singleton "else")
    -- -- _ = there (here refl) -- ✖ DOES NOT COMPUTE, AS EXPECTED!
    -- _ = ∈-∪⁺ʳ _ _ _ (∈-∪⁺ˡ _ _ _ ?)
