module Prelude.Bags.Examples where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable

private
  module ConcreteExample where
    open import Prelude.Bags
    open import Prelude.Semigroup

    _ = Bag⟨ String ⟩ ∋ singleton "sth" ◇ singleton "sth"
    _ = DecEq Bag⟨ String ⟩ ∋ it

    _ : "sth" ∈ˢ (singleton "else" ◇ singleton "sth" ◇ singleton "else")
    _ = auto -- ✓ COMPUTES, AS EXPECTED!

  module AbstractExample where
    open import Prelude.Bags.Abstract

    _ : "sth" ∈ˢ (singleton "else" ∪ singleton "sth" ∪ singleton "else")
    -- _ = auto -- there $′ here refl -- ✖ DOES NOT COMPUTE, AS EXPECTED!
    _ = ∈-∪⁺ʳ _ _ _
      $ ∈-∪⁺ˡ _ _ _
      $ singleton∈ˢ .proj₂ refl
