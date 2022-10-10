open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.Apartness
open import Prelude.Setoid renaming (_≈_ to _≈₀_)
open import Prelude.Ord
open import Prelude.Decidable
open import Prelude.Monoid

module Prelude.Maps.Abstract {K V : Type} ⦃ _ : DecEq K ⦄ ⦃ _ : DecEq V ⦄
  ⦃ _ : Ord V ⦄
  ⦃ _ : _≤_ {A = V} ⁇² ⦄
  ⦃ _ : _<_ {A = V} ⁇² ⦄
  ⦃ _ : Monoid V ⦄
  where

import Prelude.Maps.Concrete as Imp
open import Prelude.Maps.Abstract.Interface

-- T0D0: different notions of _≈_ map equivalence
-- abstract
--   imp : Mapᴵ K V 0ℓ
--   imp = record {Imp}

--   open Mapᴵ imp public
