------------------------------------------------------------------------
-- Non-empty lists.

{-# OPTIONS --safe #-}
module Prelude.Lists.NonEmpty where

open import Prelude.Init; open SetAsType
open L.NE
open import Prelude.Bifunctor
open import Prelude.Null
open import Prelude.Lists.Empty

private variable A : Type ℓ; x y : A; xs : List⁺ A

-- List⁺
All⁺ : Pred A ℓ′ → List⁺ A → Type _
All⁺ P = All P ∘ toList

toList⁺ : ∀ (xs : List A) → xs ≢ [] → List⁺ A
toList⁺ []       ¬[] = ⊥-elim $ ¬[] refl
toList⁺ (x ∷ xs) _   = x ∷ xs

toList∘toList⁺ : ∀ {A : Type ℓ} (xs : List A) (xs≢[] : ¬Null xs)
  → toList (toList⁺ xs xs≢[]) ≡ xs
toList∘toList⁺ [] ¬n     = ⊥-elim $ ¬n refl
toList∘toList⁺ (_ ∷ _) _ = refl

All⇒All⁺ : ∀ {A : Type ℓ} {xs : List A} {p : ¬Null xs} {P : Pred₀ A}
  → All P xs
  → All⁺ P (toList⁺ xs p)
All⇒All⁺ {xs = xs} {p} ∀P rewrite toList∘toList⁺ xs p = ∀P

last-∷ʳ : ∀ {xs : List A} → L.last (xs L.∷ʳ x) ≡ just x
last-∷ʳ {xs = []} = refl
last-∷ʳ {xs = _ ∷ []} = refl
last-∷ʳ {xs = _ ∷ xs@(_ ∷ _)} = last-∷ʳ {xs = xs}

∷ʳ-≗ : ∀ {xs : List A} → L.NE.toList (xs L.NE.∷ʳ x) ≡ (xs L.∷ʳ x)
∷ʳ-≗ {xs = []} = refl
∷ʳ-≗ {xs = _ ∷ []} = refl
∷ʳ-≗ {xs = _ ∷ _ ∷ _} = refl

last′ : ∀ {xs : List⁺ A} → SnocView xs → A
last′ (_ ∷ʳ′ y) = y

last′≡ : ∀ {xs : List⁺ A} → last xs ≡ last′ (snocView xs)
last′≡ {xs = xs} with _ ∷ʳ′ _ ← snocView xs = refl

snocView-∷⁺ : last′ (snocView (x ∷⁺ xs)) ≡ last′ (snocView xs)
snocView-∷⁺ {xs = _ ∷ xs} with L.initLast xs
... | [] = refl
... | _ L.∷ʳ′ _ = refl

last-∷ : last (x ∷⁺ xs) ≡ last xs
last-∷ {x = x} {xs = xs} =
  begin last (x ∷⁺ xs)             ≡⟨ last′≡ {xs = x ∷⁺ xs} ⟩
        last′ (snocView (x ∷⁺ xs)) ≡⟨ snocView-∷⁺ {xs = xs} ⟩
        last′ (snocView xs)        ≡˘⟨ last′≡ {xs = xs} ⟩
        last xs                    ∎ where open ≡-Reasoning

All⁺-last : ∀ {P : Pred₀ A} → All⁺ P xs → P (last xs)
All⁺-last {xs = x ∷ []}     (px ∷ []) = px
All⁺-last {xs = x ∷ y ∷ xs} (_  ∷ ∀p) rewrite last-∷ {x = x}{y ∷ xs} = All⁺-last ∀p
