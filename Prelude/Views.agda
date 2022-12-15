{-# OPTIONS --safe #-}
module Prelude.Views where

open import Prelude.Init; open SetAsType

private variable A : Type ℓ

record _▷_ (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  field
    view : A → B
    unview : B → A
    unview∘view : ∀ x → unview (view x) ≡ x
    view∘unview : ∀ y → view (unview y) ≡ y

open _▷_ ⦃...⦄ public

view_as_ : A → (B : Type ℓ′) ⦃ _ : A ▷ B ⦄ → B
view x as B = view {B = B} x
