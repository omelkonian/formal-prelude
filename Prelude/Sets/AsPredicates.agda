------------------------------------------------------------------------
-- Sets as characteristic functions.
------------------------------------------------------------------------

open import Prelude.Init; open SetAsType
open import Prelude.General

import Relation.Unary as U

module Prelude.Sets.AsPredicates {A : Type} where

Set' : Type₁
Set' = Pred₀ A

infixr 8 _─_
infixr 7 _∩_
infixr 6 _∪_
infix 4 _∈ˢ_

∅ : Set'
∅ = U.∅

singleton : A → Set'
singleton = U.｛_｝

_∈ˢ_ : A → Set' → Type
_∈ˢ_ = U._∈_

singleton∈ˢ : ∀ {x x′} → x′ ∈ˢ singleton x ↔ x′ ≡ x
singleton∈ˢ = (λ{ refl → refl }) , λ{ refl → refl }

∁ : Op₁ Set'
∁ = U.∁

_─_ _∪_ _∩_ : Op₂ Set'
_∪_ = U._∪_
_∩_ = U._∩_
s ─ s′ = s ∩ ∁ s′

_♯_ : Rel₀ Set'
s ♯ s′ = ∀ {k} → ¬ ((k ∈ˢ s) × (k ∈ˢ s′))

∈-∪⁻ : ∀ x xs ys → x ∈ˢ (xs ∪ ys) → x ∈ˢ xs ⊎ x ∈ˢ ys
∈-∪⁻ _ _ _ (inj₁ p) = inj₁ p
∈-∪⁻ _ _ _ (inj₂ p) = inj₂ p

∈-∪⁺ˡ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ (xs ∪ ys)
∈-∪⁺ˡ _ _ _ = inj₁

∈-∪⁺ʳ : ∀ x xs ys → x ∈ˢ ys → x ∈ˢ (xs ∪ ys)
∈-∪⁺ʳ _ _ _ = inj₂

∈-∩⁺ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ ys → x ∈ˢ (xs ∩ ys)
∈-∩⁺ _ _ _ = _,_

∈-∩⁻ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → (x ∈ˢ xs) × (x ∈ˢ ys)
∈-∩⁻ _ _ _ = id

∈-─⁻ : ∀ x xs ys → x ∈ˢ (xs ─ ys) → x ∈ˢ xs
∈-─⁻ _ _ _ = proj₁

∈-─⁺ : ∀ x xs ys → x ∈ˢ xs → ¬ x ∈ˢ ys → x ∈ˢ (xs ─ ys)
∈-─⁺ _ _ _ = _,_

∉∅ : ∀ x → ¬ x ∈ˢ ∅
∉∅ x ()
