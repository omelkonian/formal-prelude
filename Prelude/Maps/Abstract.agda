{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open import Prelude.DecEq

module Prelude.Maps.Abstract {K V : Type} ⦃ _ : DecEq K ⦄ where

import Prelude.Maps.AsPartialFunctions {K = K} {V = V} as Imp
open import Prelude.Maps.Abstract.Interface

abstract
  imp : FinMapᴵ K V 0ℓ
  imp = record {mapᴵ = record {Imp}; Imp}
  open FinMapᴵ imp public
