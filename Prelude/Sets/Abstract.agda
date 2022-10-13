open import Prelude.Init
open import Prelude.DecEq

module Prelude.Sets.Abstract {A : Set} ⦃ _ : DecEq A ⦄ where

open import Prelude.Sets.Abstract.Interface
import Prelude.Sets as Imp

abstract
  private
    imp : FinSetᴵ A 0ℓ
    imp = record {setᴵ = record {Imp}; Imp}
  open FinSetᴵ imp public
