module Prelude.Split where

open import Prelude.Init

record _-splitsInto-_ (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
  field split : A → B × B

  left _∙left right _∙right : A → B
  left  = proj₁ ∘ split; _∙left  = left
  right = proj₂ ∘ split; _∙right = right
open _-splitsInto-_ ⦃...⦄ public
