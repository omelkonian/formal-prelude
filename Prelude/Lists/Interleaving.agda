{-# OPTIONS --safe #-}
module Prelude.Lists.Interleaving where

import Data.List.Relation.Ternary.Interleaving as I

open import Prelude.Init; open SetAsType
open import Relation.Ternary

private variable A : Type ℓ

-- ** Interleaving relation, instantiated for propositional equality.
_∥_≡_ : 3Rel (List A) _
_∥_≡_ = Interleaving _≡_ _≡_

pattern keepˡ_ p = refl I.∷ˡ p
pattern keepʳ_ p = refl I.∷ʳ p
