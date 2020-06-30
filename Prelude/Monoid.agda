module Prelude.Monoid where

open import Prelude.Init
open import Prelude.Semigroup public

record Monoid (A : Set) : Set where
  field
    ε : A
    overlap {{smₐ}} : Semigroup A

open Monoid {{...}} public hiding (smₐ)

private
  variable
    A : Set

instance
  Monoid-List : Monoid (List A)
  Monoid-List .ε = []

  Monoid-Vec : Monoid (∃ (Vec A))
  Monoid-Vec .ε = 0 , []

  Monoid-String : Monoid String
  Monoid-String .ε   = ""
