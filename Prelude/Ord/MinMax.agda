-- {-# OPTIONS --safe #-}
open import Prelude.Init; open SetAsType
open import Prelude.Decidable
open import Prelude.DecEq.Core
open import Prelude.Lists
open import Prelude.InferenceRules

open import Prelude.Ord.Core
open import Prelude.Ord.Dec

module Prelude.Ord.MinMax {A : Type ℓ} ⦃ _ : Ord A ⦄ ⦃ _ : DecOrd A ⦄ where

min max : Op₂ A
min x y = if ⌊ x ≤? y ⌋ then x else y
max x y = if ⌊ y ≤? x ⌋ then x else y

minimum maximum : A → List A → A
minimum = foldl min
maximum = foldl max

minimum⁺ maximum⁺ : List⁺ A → A
minimum⁺ (x ∷ xs) = minimum x xs
maximum⁺ (x ∷ xs) = maximum x xs

module _ {x} {y} {ys : List A} where

  minimum-skip :
    x ≤ y
    ─────────────────────────────────
    minimum x (y ∷ ys) ≡ minimum x ys
  minimum-skip x≤ rewrite dec-yes (x ≤? y) x≤ .proj₂ = refl

  maximum-skip :
    y ≤ x
    ─────────────────────────────────
    maximum x (y ∷ ys) ≡ maximum x ys
  maximum-skip y≤ rewrite dec-yes (y ≤? x) y≤ .proj₂ = refl

postulate
  ∀≤max⁺ : ∀ (xs : List⁺ A) → All⁺ (_≤ maximum⁺ xs) xs
  ∀≤max : ∀ x (xs : List A) → All (_≤ maximum x xs) xs

∀≤⇒≡max : ∀ {x} {xs : List A} →
  All (_≤ x) xs
  ────────────────
  x ≡ maximum x xs
∀≤⇒≡max [] = refl
∀≤⇒≡max {x = x} {xs = y ∷ xs} (py ∷ p) =
  begin x                  ≡⟨ ∀≤⇒≡max {xs = xs} p ⟩
        maximum x xs       ≡˘⟨ maximum-skip {ys = xs} py ⟩
        maximum x (y ∷ xs) ∎ where open ≡-Reasoning
