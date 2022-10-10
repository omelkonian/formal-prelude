open import Prelude.Init
open import Prelude.DecEq

module Prelude.Bags.Abstract {A : Set} ⦃ _ : DecEq A ⦄ where

import Prelude.Bags.Concrete.AsMaps {A = A} as Imp
open import Prelude.Bags.Abstract.Interface

-- abstract
--   imp : Bagᴵ A 0ℓ
--   imp = record {Imp}

--   open Bagᴵ imp public
