module Prelude.Maps.Concrete.Example where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.FromList
open import Prelude.Semigroup
open import Prelude.Maps.Concrete

k = 0; k′ = 1
k↦_  = (ℕ → Map⟨ ℕ ↦ ℕ ⟩) ∋ singleton ∘ (k ,_)
k′↦_ = (ℕ → Map⟨ ℕ ↦ ℕ ⟩) ∋ singleton ∘ (k′ ,_)

-- ** singleton

_ = singleton (k , 10) ≡ fromList [ k , 10 ]
  ∋ refl

-- ** _∪_

_ = (k↦ 10 ∪ k′↦ 20) ≡ fromList ((k , 10) ∷ (k′ , 20) ∷ [])
  ∋ refl

_ = (k↦ 10 ∪ k↦ 20) ≡ singleton (k , 20)
  ∋ refl

-- ** insert/insertWith

_ = insert (k′ , 20) (k↦ 10) ≡ (k↦ 10 ∪ k′↦ 20)
  ∋ refl
_ = insert (k , 20) (k↦ 10) ≡ k↦ 20
  ∋ refl

_ = insertWith _+_ (k′ , 20) (k↦ 10) ≡ (k↦ 10 ∪ k′↦ 20)
  ∋ refl
_ = insertWith _+_ (k , 20) (k↦ 10) ≡ (k↦ 30)
  ∋ refl

instance _ = Semigroup-ℕ-+
_ = (k↦ 10 ◇ k↦ 20) ≡ (k↦ 30)
  ∋ refl
