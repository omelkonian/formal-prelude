{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Lists.Dec
open import Prelude.Orders
open import Prelude.Ord
open import Prelude.Irrelevance

module Prelude.Maps.AsSortedUniqueLists
  {K : Type ℓ}
  ⦃ _ : DecEq K ⦄
  ⦃ _ : Ord K ⦄
  ⦃ _ : DecOrd K ⦄
  ⦃ _ : OrdLaws K ⦄
  ⦃ _ : ·² _≤_ {A = K} ⦄
  ⦃ _ : ·² _<_ {A = K} ⦄

  {V : Type ℓ}
  ⦃ _ : DecEq V ⦄
  ⦃ _ : Ord V ⦄
  ⦃ _ : DecOrd V ⦄
  ⦃ _ : OrdLaws V ⦄
  ⦃ _ : ·² _≤_ {A = V} ⦄
  ⦃ _ : ·² _<_ {A = V} ⦄
  where

open import Prelude.Ord.Product

Map : Type _
Map = Σ (List (K × V)) (Sorted Unary.∩ (·Unique ∘ map proj₁))
syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

private
  ·-helper : Irrelevant¹ {A = List (K × V)}
          $ Sorted Unary.∩ (·Unique ∘ map proj₁)
  ·-helper {xs} (sorted-xs , uniq-xs) (sorted-xs′ , uniq-xs′)
    rewrite ∀≡ ⦃ ·Linked ⦃ ·-≤× {A = K} {B = V} ⦄ ⦄ sorted-xs sorted-xs′
          | ∀≡ uniq-xs uniq-xs′
          = refl

postulate
  Unique-map∘sort∘nubBy : ∀ (xs : List (K × V)) →
    Unique $ map proj₁ $ sort $ nubBy proj₁ xs
-- (L.Uniq.map⁺ {!!} $ Unique-sort⁺ $ Unique-nubBy proj₁ xs)

instance
  DecEq-Map : DecEq Map
  DecEq-Map ._≟_ (xs , p) (ys , q)
    with xs ≟ ys
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl rewrite ·-helper p q = yes refl

  ToList-Map : ToList Map (K × V)
  ToList-Map .toList = proj₁

  FromList-Map : FromList (K × V) (const Map)
  FromList-Map .fromList xs
    = sort (nubBy proj₁ xs) , sort-↗ (nubBy proj₁ xs)
    , Unique⇒·Unique (Unique-map∘sort∘nubBy xs)
