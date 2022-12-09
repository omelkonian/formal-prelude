open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Null
open import Prelude.Lists.Permutations
open import Prelude.Lists.Empty

open import Prelude.Ord.Core
open import Prelude.Ord.Dec

module Prelude.Ord.Sort {A : Type ℓ}
  ⦃ _ : Ord A ⦄ ⦃ _ : OrdLaws A ⦄
  ⦃ _ : DecEq A ⦄ ⦃ _ : DecOrd A ⦄
  where

private
  TO = record {Carrier = A ; _≈_ = _ ; _≤_ =  _≤_ ; isTotalOrder = isTotalOrder}
  DTO = record {Carrier = A ; _≈_ = _ ; _≤_ =  _≤_ ; isDecTotalOrder = isDecTotalOrder}

import Data.List.Relation.Unary.Sorted.TotalOrder TO as S
import Data.List.Relation.Unary.Sorted.TotalOrder.Properties as SP
open import Data.List.Relation.Unary.Sorted.TotalOrder TO public
  using (Sorted)
  renaming
    ( head to Sorted-head
    ; tail to Sorted-tail
    ; irrelevant to Sorted-irrelevant
    )

open import Data.List.Sort.MergeSort DTO public
  using (sort; sort-↗; sort-↭)

instance
  Dec-Sorted : Sorted ⁇¹
  Dec-Sorted .dec = S.sorted? _≤?_ _

Sorted? = Decidable¹ Sorted ∋ dec¹

private variable x : A; xs : List A; P : Pred A ℓ′

Unique-sort⁺ : Unique xs → Unique (sort xs)
Unique-sort⁺ = Unique-resp-↭ (↭-sym $ sort-↭ _)

Sorted-filter⁺ : (P? : Decidable¹ P) → Sorted xs → Sorted (filter P? xs)
Sorted-filter⁺ P? = SP.filter⁺ TO P?

postulate Sorted⇒sort-id : Sorted xs → sort xs ≡ xs

AllPairs⇒Sorted = SP.AllPairs⇒Sorted TO
Sorted⇒AllPairs = SP.Sorted⇒AllPairs TO

open L.Mem

∈-sort : x ∈ xs ↔ x ∈ sort xs
∈-sort = L.Perm.∈-resp-↭ (↭-sym $ sort-↭ _) , L.Perm.∈-resp-↭ (sort-↭ _)

∈-sort⁺ : x ∈ xs → x ∈ sort xs
∈-sort⁺ = ∈-sort .proj₁

∈-sort⁻ : x ∈ sort xs → x ∈ xs
∈-sort⁻ = ∈-sort .proj₂

Null-sort : Null xs ↔ Null (sort xs)
Null-sort = Null-↭ (↭-sym $ sort-↭ _) , Null-↭ (sort-↭ _)

Null-sort⁺ : Null xs → Null (sort xs)
Null-sort⁺ = Null-sort .proj₁

Null-sort⁻ : Null (sort xs) → Null xs
Null-sort⁻ = Null-sort .proj₂
