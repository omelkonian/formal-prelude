{-# OPTIONS --safe #-}
module Prelude.Lists.Prefix where

open import Prelude.Init; open SetAsType

private variable A : Type ℓ

-- ** Prefix relation, instantiated for propositional equality.
Prefix≡ : List A → List A → Type _
Prefix≡ = Prefix _≡_
