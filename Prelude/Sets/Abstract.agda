{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open import Prelude.DecEq.Core

module Prelude.Sets.Abstract {A : Type} ⦃ _ : DecEq A ⦄ where

open import Prelude.Sets.Abstract.Interface
import Prelude.Sets as Imp

abstract
  private
    imp : FinSetᴵ A 0ℓ
    imp = record {setᴵ = record {Imp}; Imp}
  open FinSetᴵ imp public
