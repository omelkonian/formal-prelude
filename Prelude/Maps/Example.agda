module Prelude.Maps.Example where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Maps
open import Prelude.Nary

_ : Map⟨ String ↦ ℕ ⟩
_ = singleton ("one" , 1) ∪ singleton ("two" , 2)
