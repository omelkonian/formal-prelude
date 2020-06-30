module Prelude.Semigroup where

open import Prelude.Init

record Semigroup (A : Set) : Set where
  infixr 5 _◇_ _<>_
  field
    _◇_ : A → A → A
  _<>_ = _◇_

open Semigroup {{...}} public

private
  variable
    A : Set

instance
  Semigroup-List : Semigroup (List A)
  Semigroup-List ._◇_ = _++_

  Semigroup-List⁺ : Semigroup (List⁺ A)
  Semigroup-List⁺ ._◇_ = _⁺++⁺_

  Semigroup-∃Vec : Semigroup (∃ (Vec A))
  Semigroup-∃Vec ._◇_ (_ , v) (_ , v′) = _ , (v V.++ v′)

  Semigroup-String : Semigroup String
  Semigroup-String ._◇_ = Str._++_
