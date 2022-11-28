open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Orders
open import Prelude.Ord
open import Prelude.Irrelevance

module Prelude.Bags.AsSortedLists
  {A : Type ℓ}
  ⦃ _ : DecEq A ⦄
  ⦃ _ : Ord A ⦄
  ⦃ _ : _≤_ {A = A} ⁇² ⦄
  ⦃ _ : TotalOrder {A = A} _≤_ ⦄
  ⦃ _ : ·² _≤_ {A = A} ⦄
  where

Bag : Type _
Bag = Σ (List A) Sorted
syntax Bag {A = A} = Bag⟨ A ⟩

private variable
  R : Rel A ℓ′

instance
  DecEq-Bag : DecEq Bag
  DecEq-Bag ._≟_ (xs , p) (ys , q)
    with xs ≟ ys
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl rewrite ∀≡ p q = yes refl

  ToList-Bag : ToList Bag A
  ToList-Bag .toList = proj₁

  FromList-Bag : FromList A Bag
  FromList-Bag .fromList xs = sort xs , sort-↗ xs
