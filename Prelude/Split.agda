{-# OPTIONS --safe #-}
module Prelude.Split where

open import Prelude.Init; open SetAsType

record _-splitsInto-_ (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  field split : A → B × B

  left _∙left right _∙right : A → B
  left  = proj₁ ∘ split; _∙left  = left
  right = proj₂ ∘ split; _∙right = right
open _-splitsInto-_ ⦃...⦄ public
