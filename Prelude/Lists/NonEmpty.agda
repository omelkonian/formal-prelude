------------------------------------------------------------------------
-- Non-empty lists.

module Prelude.Lists.NonEmpty where

open import Prelude.Init
open import Prelude.Null
open L.NE using (last; toList)
open import Prelude.Lists.Empty

private variable A : Set ℓ

-- List⁺
All⁺ : Pred₀ A → List⁺ A → Set _
All⁺ P = All P ∘ toList

toList⁺ : ∀ (xs : List A) → xs ≢ [] → List⁺ A
toList⁺ []       ¬[] = ⊥-elim $ ¬[] refl
toList⁺ (x ∷ xs) _   = x ∷ xs

toList∘toList⁺ : ∀ {A : Set ℓ} (xs : List A) (xs≢[] : ¬Null xs)
  → toList (toList⁺ xs xs≢[]) ≡ xs
toList∘toList⁺ [] ¬n     = ⊥-elim $ ¬n refl
toList∘toList⁺ (_ ∷ _) _ = refl

All⇒All⁺ : ∀ {A : Set ℓ} {xs : List A} {p : ¬Null xs} {P : Pred₀ A}
  → All P xs
  → All⁺ P (toList⁺ xs p)
All⇒All⁺ {xs = xs} {p} ∀P rewrite toList∘toList⁺ xs p = ∀P

postulate
  last-∷ : ∀ {x : A} {xs : List⁺ A} → last (x ∷⁺ xs) ≡ last xs

All⁺-last : {xs : List⁺ A} {P : Pred₀ A}
  → All⁺ P xs
  → P (last xs)
All⁺-last {xs = x ∷ []}     (px ∷ []) = px
All⁺-last {xs = x ∷ y ∷ xs} (_  ∷ ∀p) rewrite last-∷ {x = x}{y ∷ xs} = All⁺-last ∀p
