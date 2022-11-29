module Prelude.Ord.String where

import Data.List.Relation.Binary.Lex.Strict as StrictLex

open import Prelude.Init; open SetAsType
open import Prelude.Decidable
open import Prelude.DecEq

open import Prelude.Orders
open import Prelude.Ord.Core

instance
  Ord-String : Ord String
  Ord-String = λ where
    .relℓ → _
    ._≤_ → Str._≤_
    ._<_ → Str._<_

-- T0D0: cannot declare these as instances without breaking instance resolution.
module String-DecOrd where
  -- instance
  DecOrd-String : _≤_ ⁇²
  DecOrd-String .dec = StrictLex.≤-decidable _≟_ Ch._<?_ _ _

  DecStrictOrd-String : _<_ ⁇²
  DecStrictOrd-String .dec = StrictLex.<-decidable _≟_ Ch._<?_ _ _

  postulate
    ≤-to-<-String : NonStrictToStrict {A = String} _≤_ _<_
  -- ≤-to-<-String .<⇔≤∧≢ = ?

    StrictPartialOrderString-< : StrictPartialOrder {A = String} _<_
  -- StrictPartialOrderString-< = λ where
  --   .<-irrefl  → λ x≡y x<y → StrictLex.<-irreflexive <-irrefl {!!} {!x<y!}
  --   .<-trans   → {!!}
  --   .<-resp₂-≡ → {!!}

    PreorderString-≤ : Preorder {A = String} _≤_
  -- PreorderString-≤ = λ where
  --   .≤-refl  → StrictLex.≤-reflexive <-irrefl {!!} {!!}
  --   .≤-trans → StrictLex.≤-transitive PropEq.isEquivalence <-resp₂-≡ {!_<_!}

    PartialOrderString-≤ : PartialOrder {A = String} _≤_
  -- PartialOrderString-≤ .≤-antisym = {!!}

    TotalOrderString-≤ : TotalOrder {A = String} _≤_
  -- TotalOrderString-≤ .≤-total = {!!}

    StrictTotalOrderString-< : StrictTotalOrder {A = String} _<_
  -- StrictTotalOrderString-< = λ where
  --   .<-cmp → {!!}

    NonStrictToStrict-String : NonStrictToStrict {A = String} _≤_ _<_
  -- NonStrictToStrict-String .<⇔≤∧≢ = ?
