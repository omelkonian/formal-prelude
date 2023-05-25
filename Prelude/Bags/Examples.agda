{-# OPTIONS --with-K #-}
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

  module Implementation where
    open import Prelude.Bags.AsSortedLists
    open import Prelude.Nary
    open import Prelude.ToList
    open import Prelude.FromList
    open import Prelude.Ord
    open import Prelude.Irrelevance

    _ = toList (Bag⟨ ℕ ⟩ ∋ fromList
        ⟦ 0 , 5 , 2 , 0 ⟧)
      ≡ ⟦ 0 , 0 , 2 , 5 ⟧
      ∋ refl

    -- T0D0: cover abstract signature
    -- open import Prelude.Bags.Abstract.Interface
    -- import Prelude.Bags.AsSortedLists as Imp

  module Implementation2 where
    open import Prelude.Bags.AsPartialFunctions

    _ = Bag⟨ ℕ ⟩
    _ = ∅
