module Prelude.Sets.Concrete.Example where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.DecLists
open import Prelude.Decidable
open import Prelude.FromList
open import Prelude.Semigroup
open import Prelude.Ord
open import Prelude.Apartness
open import Prelude.Sets.Concrete

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

_ : All' (_≥ 9) (x ∪ y)
_ = auto

_ : All' (_≰ 5) (x ∪ y)
_ = auto

_ : Any' (_≥ 11) (x ∪ y)
_ = auto

_ : Any' (_≱ 12) (x ∪ y)
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
