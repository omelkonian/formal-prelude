{-# OPTIONS --safe #-}
module Prelude.ToList where

open import Prelude.Init; open SetAsType
open import Prelude.Lists

record ToList (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  field toList : A → List B
  _∙toList = toList
open ToList ⦃...⦄ public

private
  variable
    A : Type ℓ
    B : Type ℓ′

instance
  ToList-List : ToList (List A) A
  ToList-List .toList = id

  ToList-List⁺ : ToList (List⁺ A) A
  ToList-List⁺ .toList = L.NE.toList

  ToList-Str : ToList String Char
  ToList-Str .toList = Str.toList

  ToList-Vec : ∀ {n} → ToList (Vec A n) A
  ToList-Vec .toList = V.toList

  ToList-↦ : ∀ {xs : List A} → ToList (xs ↦ B) (A × B)
  ToList-↦ {xs = xs} .toList f = zip xs (codom f)
