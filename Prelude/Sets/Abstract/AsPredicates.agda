------------------------------------------------------------------------
-- Sets as characteristic functions.
------------------------------------------------------------------------

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable

open import Prelude.Sets.Abstract.Interface

import Relation.Unary as U

module Prelude.Sets.Abstract.AsPredicates {A : Set} where

abstract

  Set' : Set₁
  Set' = Pred₀ A

  infixr 8 _─_
  infixr 7 _∩_
  infixr 6 _∪_
  infix 4 _∈ˢ_

  ∅ : Set'
  ∅ = U.∅

  singleton : A → Set'
  singleton = U.｛_｝

  _∈ˢ_ : A → Set' → Set
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

abstract
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

setᴵ : Setᴵ A 1ℓ
setᴵ = mkSetᴵ Set' ∅ singleton _∈ˢ_ _─_ _∪_ _∩_
              singleton∈ˢ ∈-∪⁻ ∈-∪⁺ˡ ∈-∪⁺ʳ ∈-∩⁺ ∈-∩⁻ ∈-─⁻ ∈-─⁺ ∉∅
open Setᴵ setᴵ using (_∉ˢ_; _≈ˢ_; ≈ˢ-refl; ≈ˢ-sym; ≈ˢ-trans; ≈ˢ-setoid; module ≈ˢ-Reasoning)
open Alg _≈ˢ_

abstract

  ∅─-identityʳ : RightIdentity ∅ _─_
  ∅─-identityʳ xs =
    begin xs ─ ∅   ≈⟨ ≈ˢ-refl ⟩
          xs ∩ ∁ ∅ ≈⟨ (proj₁ ∘ ∈-∩⁻ _ xs (∁ ∅) , (λ {x} x∈ → ∈-∩⁺ _ xs (∁ ∅) x∈ (∉∅ x))) ⟩
          xs ∎
    where open ≈ˢ-Reasoning

  ∅∪-identityˡ : LeftIdentity ∅ _∪_
  ∅∪-identityˡ xs = (λ x∈ → case ∈-∪⁻ _ ∅ xs x∈ of λ{ (inj₁ x∈∅) → case x∈∅ of λ (); (inj₂ x∈xs) → x∈xs} )
                  , ∈-∪⁺ʳ _ ∅ xs

  ∅∪-identityʳ : RightIdentity ∅ _∪_
  ∅∪-identityʳ xs = (λ x∈ → case ∈-∪⁻ _ xs ∅ x∈ of λ{ (inj₁ x∈xs) → x∈xs; (inj₂ x∈∅) → case x∈∅ of λ ()} )
                  , ∈-∪⁺ˡ _ xs ∅

  ∩-comm : Commutative _∩_
  ∩-comm xs ys
    = (λ x∈ → let (x∈xs , x∈ys) = ∈-∩⁻ _ xs ys x∈ in ∈-∩⁺ _ ys xs x∈ys x∈xs)
    , (λ x∈ → let (x∈ys , x∈xs) = ∈-∩⁻ _ ys xs x∈ in ∈-∩⁺ _ xs ys x∈xs x∈ys)

  ∪-comm : Commutative _∪_
  ∪-comm xs ys
    = (λ x∈ → case ∈-∪⁻ _ xs ys x∈ of λ{ (inj₁ x∈xs) → ∈-∪⁺ʳ _ ys xs x∈xs; (inj₂ x∈ys) → ∈-∪⁺ˡ _ ys xs x∈ys})
    , (λ x∈ → case ∈-∪⁻ _ ys xs x∈ of λ{ (inj₁ x∈ys) → ∈-∪⁺ʳ _ xs ys x∈ys; (inj₂ x∈xs) → ∈-∪⁺ˡ _ xs ys x∈xs})
