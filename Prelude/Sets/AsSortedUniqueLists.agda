open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.DecLists
open import Prelude.Orders
open import Prelude.Ord
open import Prelude.Irrelevance

module Prelude.Sets.AsSortedUniqueLists
  {A : Type ℓ}
  ⦃ _ : DecEq A ⦄
  ⦃ _ : Ord A ⦄ ⦃ _ : OrdLaws A ⦄
  ⦃ _ : ·² _≤_ {A = A} ⦄
  where

Set' : Type _
Set' = Σ (List A) (Sorted Unary.∩ ·Unique)
syntax Set' {A = A} = Set⟨ A ⟩

private variable
  R : Rel A ℓ′

instance
  DecEq-Set : DecEq Set'
  DecEq-Set ._≟_ (xs , p) (ys , q)
    with xs ≟ ys
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl rewrite ∀≡ p q = yes refl

  ToList-Set : ToList Set' A
  ToList-Set .toList = proj₁

  FromList-Set : FromList A Set'
  FromList-Set .fromList xs
    = sort (nub xs) , sort-↗ (nub xs)
    , Unique⇒·Unique (Unique-sort⁺ $ Unique-nub {xs = xs})
