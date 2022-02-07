module Prelude.Maps.Example where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Maps
open import Prelude.Semigroup
open import Prelude.Monoid

_ = Map⟨ String ↦ ℕ ⟩
  ∋ singleton ("one" , 1) ∪ singleton ("two" , 2)

_ = Map
  ∋ singleton ("one" , 1) ◇ singleton ("one" , 2)
  where instance _ = SemigroupLaws-ℕ-+
                 _ = MonoidLaws-ℕ-+
