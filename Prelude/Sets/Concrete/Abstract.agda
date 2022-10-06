open import Prelude.Init
open import Prelude.DecEq

module Prelude.Sets.Concrete.Abstract {A : Set} ⦃ _ : DecEq A ⦄ where

open import Prelude.Sets.Interface
import Prelude.Sets.Concrete as Imp

abstract
  imp : Setᴵ A 0ℓ
  imp = record {Imp}

  open Setᴵ imp public
