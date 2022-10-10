open import Prelude.Init
open import Prelude.DecEq

module Prelude.Sets.Abstract {A : Set} ⦃ _ : DecEq A ⦄ where

import Prelude.Sets.Concrete.Core as Imp
open import Prelude.Sets.Abstract.Interface

abstract
  imp : Setᴵ A 0ℓ
  imp = record {Imp}

  open Setᴵ imp public
