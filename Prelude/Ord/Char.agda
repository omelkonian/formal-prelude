module Prelude.Ord.Char where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable

open import Prelude.Orders
open import Prelude.Ord.Core

instance
  Ord-Char : Ord Char
  Ord-Char = λ where
    .relℓ → _
    ._≤_ → Ch._≤_
    ._<_ → Ch._<_

  postulate
    NonStrictToStrict-Char : NonStrictToStrict {A = Char} _≤_ _<_

-- T0D0: cannot declare these as instances without breaking instance resolution.
module Char-DecOrd where
  -- instance
  DecOrd-Char : _≤_ ⁇²
  DecOrd-Char .dec = _ Ch.≤? _

  DecStrictOrd-Char : _<_ ⁇²
  DecStrictOrd-Char {x}{y} .dec = x Ch.<? y

  postulate
    StrictPartialOrderChar-< : StrictPartialOrder _<_
  -- StrictPartialOrderChar-< = λ where
  --   .<-irrefl  → {!!}
  --   .<-trans   → {!!}
  --   .<-resp₂-≡ → {!!}

    PreorderChar-≤ : Preorder _≤_
  -- PreorderChar-≤ = λ where
  --   .≤-refl  → StrictLex.≤-reflexive {!!} {!!} {!!}
  --   .≤-trans → StrictLex.≤-transitive PropEq.isEquivalence {!<-resp₂-≡!} {!!}

    PartialOrderChar-≤ : PartialOrder _≤_
  -- PartialOrderChar-≤ .≤-antisym = {!!}

    TotalOrderChar-≤ : TotalOrder _≤_
  -- TotalOrderChar-≤ .≤-total = {!!}

    StrictTotalOrderChar-< : StrictTotalOrder _<_
  -- StrictTotalOrderChar-< = λ where
  --   .<-cmp → {!!}
