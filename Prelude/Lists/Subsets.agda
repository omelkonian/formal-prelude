{-# OPTIONS --safe #-}
open import Prelude.Init; open SetAsType

module Prelude.Lists.Subsets {A : Type ℓ} where

infix 4 _⊆′_
record _⊆′_ (xs ys : List A) : Type ℓ where
  constructor mk⊆
  field unmk⊆ : xs ⊆ ys
open _⊆′_ public
