{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open import Prelude.DecEq

module Prelude.Bags.Abstract {A : Type} ⦃ _ : DecEq A ⦄ where

import Prelude.Bags.AsMaps {A = A} as Imp
  hiding (singleton∈ˢ) renaming (singleton∈ˢ′ to singleton∈ˢ)
open import Prelude.Bags.Abstract.Interface

abstract
  imp : Bagᴵ A 0ℓ
  imp = record {Imp}
  open Bagᴵ imp public
