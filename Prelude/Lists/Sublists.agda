{-# OPTIONS --safe #-}
module Prelude.Lists.Sublists where

open import Prelude.Init; open SetAsType

module L-Sublists where
  open import Data.List.Relation.Binary.Sublist.Propositional public
  open import Data.List.Relation.Binary.Sublist.Propositional.Properties public

open L-Sublists using ([]) renaming
  ( _⊆_ to _⊑_
  ; _⊈_ to _⋢_
  ; _⊇_ to _⊒_
  ; _⊉_ to _⋣_
  ; _∷ʳ_ to keep⊑
  ; _∷_  to drop⊑
  ) public
pattern drop≡ x p = drop⊑ {x} refl p

map⊑ : ∀ {X : Type ℓ} {xs ys : List X} → Op₁ X → ys ⊑ xs → List X
map⊑ f = λ where
  []          → []
  (keep⊑ x p) → f x ∷ map⊑ f p
  (drop≡ x p) → x   ∷ map⊑ f p

remove⊑ : ∀ {X : Type ℓ} {xs ys : List X} → Op₁ X → ys ⊑ xs → List X
remove⊑ f = λ where
  []          → []
  (keep⊑ _ p) → remove⊑ f p
  (drop≡ x p) → x ∷ remove⊑ f p
