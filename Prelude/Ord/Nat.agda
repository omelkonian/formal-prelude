module Prelude.Ord.Nat where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable

open import Prelude.Orders
open import Prelude.Ord.Core

instance
  Ord-ℕ : Ord ℕ
  Ord-ℕ = record {Nat}

  DecOrd-ℕ : _≤_ ⁇²
  DecOrd-ℕ .dec = _ Nat.≤? _

  DecStrictOrd-ℕ : _<_ ⁇²
  DecStrictOrd-ℕ .dec = _ Nat.<? _

  Preorderℕ-≤ : Preorder _≤_
  Preorderℕ-≤ = record {Nat; ≤-refl = Nat.≤-reflexive refl}

  PartialOrderℕ-≤ : PartialOrder _≤_
  PartialOrderℕ-≤ = record {Nat}

  TotalOrderℕ-≤ : TotalOrder _≤_
  TotalOrderℕ-≤ = record {Nat}

  StrictPartialOrderℕ-< : StrictPartialOrder _<_
  StrictPartialOrderℕ-< = record {Nat}

  StrictTotalOrderℕ-< : StrictTotalOrder _<_
  StrictTotalOrderℕ-< = record {Nat}
