open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Nary

module Prelude.Maps {K V : Set} where

open import Prelude.Maps.Interface
import Prelude.Maps.AsPartialFunctions4 {K}{V} as M₁

open import Prelude.DecEq

open Mapᴵ (Mapᴵ K V _ ∋ record {M₁}) public
  -- renaming
  --   ( _≈_ to _≈ᵐ_
  --   ; ∅ to ∅′
  --   ; _∪_ to _∪′_
  --   ; _⁉_ to _⁉′_
  --   ; _♯_ to _♯′_
  --   )

module _ ⦃ _ : DecEq K ⦄ where
  open DecMapᴵ (DecMapᴵ K V _ ∋ record {M₁}) public
    -- renaming (singleton to singleton′)
  -- open DecEqMapᴵ (DecEqMapᴵ A _ ∋ record {M₁}) public

  _ : Map
  _ = singleton (k , v) ∪ singleton (k′ , v′)
    where
      postulate k k′ : K
                v v′ : V
