module Prelude.Lists.Count where

open import Prelude.Init
open Nat using (_≤_)
open import Prelude.Lists.Empty

private variable
  A : Set ℓ
  B : Set ℓ′
  xs ys : List A

-- count
count : ∀ {P : A → Set} → Decidable¹ P → List A → ℕ
count P? = length ∘ filter P?

postulate
  count-single : ∀ {P : A → Set} {P? : Decidable¹ P} {x xs}
    → count P? (x ∷ xs) ≡ 1
    → P x
    → All (x ≢_) xs
-- count-single {P = P} {P?} {x} {xs} count≡1 px
--   with P? x
-- ... | no ¬px = ⊥-elim $ ¬px px
-- ... | yes _  = L.All.¬Any⇒All¬ xs h
--   where
--     h : x ∉ xs
--     h x∈ = {!!}

postulate
  ⊆⇒count≤ : ∀ {P : Pred₀ A}
    → (P? : Decidable¹ P)
    → xs ⊆ ys
    → count P? xs ≤ count P? ys

  count≡0⇒null-filter : ∀ {P : Pred₀ A}
    → (P? : Decidable¹ P)
    → count P? xs ≡ 0
    → Null $ filter P? xs

  count≡0⇒All¬ : ∀ {P : Pred₀ A}
    → (P? : Decidable¹ P)
    → count P? xs ≡ 0
    → All (¬_ ∘ P) xs

  count-map⁺ : ∀ {f : A → B} {P : Pred₀ B} {P? : Decidable¹ P}
    → count (P? ∘ f) xs
    ≡ count P? (map f xs)
