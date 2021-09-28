module Prelude.Foldable where

open import Prelude.Init
open import Prelude.Monoid

record Foldable (F : Set↑) : Setω where
  field
    foldMap : ∀ {A : Set ℓ} {M : Set ℓ′} ⦃ _ : Monoid M ⦄ → (A → M) → F A → M

open Foldable ⦃ ... ⦄ public

instance
  Foldable-Maybe : Foldable Maybe
  Foldable-Maybe .foldMap f nothing  = ε
  Foldable-Maybe .foldMap f (just x) = f x

  Foldable-List : Foldable List
  Foldable-List .foldMap f [] = ε
  Foldable-List .foldMap f (x ∷ xs) = f x ◇ foldMap f xs

  Foldable-List⁺ : Foldable List⁺
  Foldable-List⁺ .foldMap f (x ∷ xs) = f x ◇ foldMap f xs
