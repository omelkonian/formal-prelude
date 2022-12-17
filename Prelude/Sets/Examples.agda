{-# OPTIONS --with-K #-}
module Prelude.Sets.Examples where

open import Prelude.Init; open SetAsType
open import Prelude.Semigroup
open import Prelude.Ord
open import Prelude.Irrelevance
open import Prelude.Apartness
open import Prelude.Nary
open import Prelude.ToList; open import Prelude.FromList
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists.Dec

private
  module Implementation1 where
    open import Prelude.Sets.Abstract.Interface
    import Prelude.Sets.AsPredicates as Imp
    module _ {A : Type} where
      _ = Setᴵ A 1ℓ ∋ record {Imp}

  module Implementation2 where
    open import Prelude.Sets.Abstract.Interface
    import Prelude.Sets.AsUniqueLists as Imp
    module _ {A : Type} ⦃ _ : DecEq A ⦄ where
      setᴵ = Setᴵ A 0ℓ ∋ record {Imp}
      _ = FinSetᴵ A 0ℓ ∋ record {setᴵ = setᴵ; Imp}

  module Implementation3 where
    open import Prelude.Sets.AsSortedUniqueLists

    _ = Set⟨ ℕ ⟩ ∋ ∅
    _ = toList (Set⟨ ℕ ⟩ ∋ fromList
        ⟦ 0 , 5 , 2 , 0 ⟧)
      ≡ ⟦ 0 , 2 , 5 ⟧
      ∋ refl

    -- T0D0: cover abstract signature
    -- open import Prelude.Sets.Abstract.Interface
    -- import Prelude.Sets.AsSortedUniqueLists as Imp

  module AbstractExample where
    open import Prelude.Sets.Abstract

    _ = Set⟨ ℕ ⟩ ∋ ∅
    _ = Set⟨ ℕ ⟩ ∋ singleton 5 ∪ singleton 10
    _ = Decidable² {A = ℕ} _∈ˢ_ ∋ _∈ˢ?_
    _ = DecEq Set⟨ ℕ ⟩ ∋ it

    _ : 1 ∈ˢ (singleton 0 ∪ singleton 1 ∪ singleton 2)
    -- _ = there (here refl) -- ✖ DOES NOT COMPUTE, AS EXPECTED!
    _ = ∈-∪⁺ʳ _ _ _ (∈-∪⁺ˡ _ _ _ (singleton∈ˢ .proj₂ refl))

  module AbstractOrderedExample where
    open import Prelude.Sets.AsSortedUniqueLists.Abstract
    -- open import Prelude.Ord.Product

    _ = Set⟨ ℕ ⟩ ∋ ∅ˢ
    _ = Set⟨ ℕ ⟩ ∋ singleton 5 ∪ singleton 10
    _ = Decidable² {A = ℕ} _∈ˢ_ ∋ _∈ˢ?_
    _ = DecEq Set⟨ ℕ ⟩ ∋ it

    _ : 1 ∈ˢ (singleton 0 ∪ singleton 1 ∪ singleton 2)
    -- _ = there (here refl) -- ✖ DOES NOT COMPUTE, AS EXPECTED!
    _ = ∈-∪⁺ʳ _ _ _ (∈-∪⁺ˡ _ _ _ (singleton∈ˢ .proj₂ refl))

  module ConcreteExample where
    open import Prelude.Sets

    _ = Set⟨ ℕ ⟩ ∋ singleton 5 ∪ singleton 10
    _ = DecEq Set⟨ ℕ ⟩ ∋ it

    _ : 1 ∈ˢ (singleton 0 ∪ singleton 1 ∪ singleton 2)
    _ = there (here refl) -- ✓ COMPUTES, AS EXPECTED!

    _ = Set⟨ ℕ ⟩ ∋ ∅

    -- ** singleton
    x = Set⟨ ℕ ⟩ ∋ singleton 10
    y = Set⟨ ℕ ⟩ ∋ singleton 11
    z = Set⟨ ℕ ⟩ ∋ singleton 0

    _ = x ≡ fromList [ 10 ]
      ∋ refl

    -- ** _∪_

    _ = (x ∪ y) ≡ fromList (10 ∷ 11 ∷ [])
      ∋ refl

    _ = (x ∪ x) ≡ fromList [ 10 ]
      ∋ refl

    -- ** _∩_

    _ = ((x ∪ y) ∩ (x ∪ z)) ≡ fromList [ 10 ]
      ∋ refl

    _ = (x ∩ y) ≡ ∅
      ∋ refl

    _ = (x ∩ z) ≡ ∅
      ∋ refl

    _ = (x ∩ y ∩ z) ≡ ∅
      ∋ refl

    -- ** All'/Any'

    _ : Allˢ (_≥ 9) (x ∪ y)
    _ = auto

    _ : Allˢ (_≰ 5) (x ∪ y)
    _ = auto

    _ : Anyˢ (_≥ 11) (x ∪ y)
    _ = auto

    _ : Anyˢ (_≱ 12) (x ∪ y)
    _ = auto

    -- ** _∈ˢ_

    _ : 10 ∈ˢ (y ∪ z ∪ x)
    _ = auto

    _ : 9 ∉ˢ (y ∪ z ∪ x)
    _ = auto

    _ : y ⊆ˢ (x ∪ y)
    _ = toWitness {Q = y ⊆?ˢ (x ∪ y)} tt

    -- ** _♯_

    _ : (x ∪ y) ♯ z
    _ = auto

    -- ** _≈_

    _ : (x ∪ y) ≈ˢ (y ∪ x)
    _ = auto

    _ : (x ∪ y ∪ y ∪ y ∪ (x ∩ z)) ≈ˢ ((x ∩ z) ∪ y ∪ x)
    _ = auto
