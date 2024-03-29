{-# OPTIONS --safe #-}
module Prelude.Foldable where

open import Prelude.Init; open SetAsType
open import Prelude.Semigroup
open import Prelude.Monoid

record Foldable (F : Type↑) : Typeω where
  field
    foldMap : ∀ {A : Type ℓ} {M : Type ℓ′}
      → ⦃ _ : Semigroup M ⦄ ⦃ _ : Monoid M ⦄
      → (A → M) → F A → M

open Foldable ⦃...⦄ public

instance
  Foldable-Maybe : Foldable Maybe
  Foldable-Maybe .foldMap f nothing  = ε
  Foldable-Maybe .foldMap f (just x) = f x

  Foldable-List : Foldable List
  Foldable-List .foldMap f = go where go = λ where
    [] → ε
    (x ∷ xs) → f x ◇ go xs

  Foldable-List⁺ : Foldable List⁺
  Foldable-List⁺ .foldMap f (x ∷ xs) = f x ◇ foldMap f xs
