module Prelude.Sets.Instances where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Membership

private variable A : Set

-- [T0D0] this won't work, unless we refine the definition of Setᴵ
-- instance
--   M-Set : ⦃ _ : DecEq A ⦄ → HasMembership (λ A → Set⟨ A ⟩)
--   M-Set ._∈_ = ?
