module Prelude.Monoid where

open import Prelude.Init

record Monoid (A : Set) : Set where
  infixr 5 _◇_ _<>_
  field
    ε : A
    _◇_ : A → A → A
  _<>_ = _◇_

open Monoid {{...}} public

instance
  Monoid-List : ∀ {A : Set} → Monoid (List A)
  Monoid-List .ε   = []
  Monoid-List ._◇_ = _++_

  Monoid-String : Monoid String
  Monoid-String .ε   = ""
  Monoid-String ._◇_ = Str._++_
