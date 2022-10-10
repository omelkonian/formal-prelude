open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Semigroup

module Prelude.Maps.Abstract.TestImplementations {K V : Set} where

open import Prelude.Maps.Abstract.Interface                   -- abstract interface
import Prelude.Maps.Abstract.AsPartialFunctions4 {K}{V} as M₁ -- implementations
module Imp = M₁                                               -- pick an implementation

open Mapᴵ {K = K} {V = V} record {Imp} public
open DecMapᴵ record {Imp} public

private wb = WithBuildᴵ ∋ record {Imp}
open WithBuildᴵ wb public

module _ ⦃ _ : DecEq K ⦄ where
  open WithSingletonᴵ record {Imp} public
  open CommandDSL wb public
  -- open DecEqMapᴵ {K = K} {V = V} record {Imp} public
