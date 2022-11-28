module Prelude.Ord.Int where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable

open import Prelude.Orders
open import Prelude.Ord.Core

instance
  Ord-ℤ : Ord ℤ
  Ord-ℤ = record {Integer}

  DecOrd-ℤ : _≤_ ⁇²
  DecOrd-ℤ .dec = _ Integer.≤? _

  DecStrictOrd-ℤ : _<_ ⁇²
  DecStrictOrd-ℤ .dec = _ Integer.<? _

  Preorderℤ-≤ : Preorder _≤_
  Preorderℤ-≤ = record {Integer; ≤-refl = Integer.≤-reflexive refl}

  PartialOrderℤ-≤ : PartialOrder _≤_
  PartialOrderℤ-≤ = record {Integer}

  TotalOrderℤ-≤ : TotalOrder _≤_
  TotalOrderℤ-≤ = record {Integer}

  StrictPartialOrderℤ-< : StrictPartialOrder _<_
  StrictPartialOrderℤ-< = record {Integer; <-resp₂-≡ = subst (_ <_) , subst (_< _)}

  StrictTotalOrderℤ-< : StrictTotalOrder _<_
  StrictTotalOrderℤ-< = record {Integer}
