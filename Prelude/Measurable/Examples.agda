module Prelude.Measurable.Examples where

open import Prelude.Init; open SetAsType
open Nat
open import Prelude.Nats.Postulates
open import Prelude.Measurable


private variable A : Type ℓ

instance _ = Measurable-List₁

list>0 : ∀ ⦃ _ : Measurable A ⦄ (xs : List A)
  → ∣ xs ∣ > 0
list>0 [] = s≤s z≤n
list>0 (x ∷ xs) with ∣ x ∣
... | 0     = list>0 xs
... | suc _ = s≤s z≤n

≺ᵐ-∷ : ⦃ _ : Measurable A ⦄ (x : A) (xs : List A)
  → (x ≺ᵐ (x ∷ xs))
≺ᵐ-∷ x xs = x<x+y ∣ x ∣ (list>0 xs)
