{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.General
open import Prelude.Ord

module Prelude.Bags.AsMaps {A : Type} ⦃ _ : DecEq A ⦄ where

open import Prelude.Maps {K = A} {V = ℕ} as Map public
  using
  ( ∅; _∪_; _⁉_
  )
  renaming
  ( Map to Bag
  ; DecEq-Map to DecEq-Bag
  ; _∈ᵈ_ to _∈ˢ_; _∉ᵈ_ to _∉ˢ_
  ; ∈ᵈ-∪⁺ˡ to ∈ˢ-∪⁺ˡ
  ; ∈ᵈ-∪⁺ʳ to ∈ˢ-∪⁺ʳ
  )

singleton : A → Bag
singleton x = Map.singleton (x , 1)

singleton∈ˢ : ∀ {x x′} → x′ ∈ˢ singleton x ↔ x′ ≡ x
singleton∈ˢ = (λ where (here refl) → refl)
            , (λ where refl → here refl)


occurs : Bag → A → ℕ
occurs b x = fromMaybe 0 (b ⁉ x)

postulate
  _─_ : Op₂ Bag
  scale : Bag → ℕ → Bag

_∈ˢ′_ : A → Bag → Type
x ∈ˢ′ b = occurs b x > 0

postulate
  ∈⇒∈′ : _∈ˢ_ ⇒² _∈ˢ′_
  ∈′⇒∈ : _∈ˢ′_ ⇒² _∈ˢ_

∈⇔∈′ : _∈ˢ_ ⇔² _∈ˢ′_
∈⇔∈′ = ∈⇒∈′ , ∈′⇒∈

postulate
  occurs-∪ : ∀ x xs ys → occurs (xs ∪ ys) x ≡ occurs xs x + occurs ys x
  occurs-─ : ∀ x xs ys → occurs (xs ─ ys) x ≡ occurs xs x ∸ occurs ys x
  occurs-scale : ∀ x xs n → occurs (scale xs n) x ≡ occurs xs x * n

singleton∈ˢ′ : ∀ {x x′} → x′ ∈ˢ′ singleton x ↔ x′ ≡ x
singleton∈ˢ′ {x}{x′} =
  let ↝ , ↜ = singleton∈ˢ {x}{x′}
  in ↝ ∘ ∈′⇒∈ , ∈⇒∈′ ∘ ↜
