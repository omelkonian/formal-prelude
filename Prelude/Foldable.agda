module Prelude.Foldable where

open import Prelude.Init
open import Prelude.Monoid

record Foldable (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    foldMap : ∀ {A : Set ℓ} {M : Set} ⦃ _ : Monoid M ⦄ → (A → M) → F A → M

open Foldable ⦃ ... ⦄ public

instance
  Foldable-Maybe : Foldable {ℓ} Maybe
  Foldable-Maybe .foldMap f nothing  = ε
  Foldable-Maybe .foldMap f (just x) = f x

  Foldable-List : Foldable {ℓ} List
  Foldable-List .foldMap f [] = ε
  Foldable-List .foldMap f (x ∷ xs) = f x ◇ foldMap f xs
