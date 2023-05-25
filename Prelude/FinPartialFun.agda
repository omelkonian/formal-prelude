{-# OPTIONS --with-K #-}
module Prelude.FinPartialFun where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Apartness
open import Prelude.Decidable
open import Prelude.Semigroup
open import Prelude.PartialSemigroup renaming (_◆_ to _∙_)
open import Prelude.Monoid
open import Prelude.Separated

-- ** using Prelude.Sets

open import Prelude.Sets
open import Prelude.DecEq

_⇀ᶠⁱⁿ_ : (A : Type) ⦃ _ : DecEq A ⦄ → Type → Type
A ⇀ᶠⁱⁿ B = Σ Set⟨ A ⟩ (_↦ B)

private variable A B : Type

open import Prelude.Setoid

module _ {A B : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : LawfulSetoid B ⦄ where


  _∪ᶠⁱⁿ_ : Op₂ (A ⇀ᶠⁱⁿ B)
  (xs , f) ∪ᶠⁱⁿ (ys , g) = xs ∪ ys , f ∪/↦ g

  ∅ᶠⁱⁿ : A ⇀ᶠⁱⁿ B
  ∅ᶠⁱⁿ = ∅ , (mk↦ ⊥-elim ∘ ∉∅ _)

  instance
    Semigroup-⇀ᶠⁱⁿ : Semigroup (A ⇀ᶠⁱⁿ B)
    Semigroup-⇀ᶠⁱⁿ ._◇_ = _∪ᶠⁱⁿ_

    Setoid-⇀ᶠⁱⁿ : ISetoid (A ⇀ᶠⁱⁿ B)
    Setoid-⇀ᶠⁱⁿ = λ where
      .relℓ → _
      ._≈_ (xs , mk↦_ f) (ys , mk↦_ g) →
        ∃ λ (xs≈ : xs ≈ ys) →
          ∀ x → (x∈ : x ∈ˢ xs) → f x∈ ≈ g (xs≈ .proj₁ x∈)

    Monoid-⇀ᶠⁱⁿ : Monoid (A ⇀ᶠⁱⁿ B)
    Monoid-⇀ᶠⁱⁿ .ε = ∅ᶠⁱⁿ

    postulate
      _ : SetoidLaws (A ⇀ᶠⁱⁿ B)
      _ : SemigroupLaws (A ⇀ᶠⁱⁿ B)
      _ : MonoidLaws (A ⇀ᶠⁱⁿ B)

    //-⇀ᶠⁱⁿ : (A ⇀ᶠⁱⁿ B) // (A ⇀ᶠⁱⁿ B)
    //-⇀ᶠⁱⁿ = λ where ._♯_ → _♯_ on proj₁

    -- Dec-//-⇀ᶠⁱⁿ : _♯_ {A = A ⇀ᶠⁱⁿ B} ⁇²
    -- Dec-//-⇀ᶠⁱⁿ {f}{g} .dec = f .proj₁ ♯ˢ? g .proj₁

  _♯ᶠⁱⁿ_ = Rel₀ (A ⇀ᶠⁱⁿ B) ∋ _♯_

  _♯ᶠⁱⁿ?_ : Decidable² _♯ᶠⁱⁿ_
  f ♯ᶠⁱⁿ? g = f .proj₁ ♯ˢ? g .proj₁ -- Dec-//-⇀ᶠⁱⁿ {f}{g} .dec

  open ≈-Reasoning

  postulate _ : Separated (A ⇀ᶠⁱⁿ B)
  -- _ = λ where
  --   .ε → ∅ᶠⁱⁿ
  --   ._∙_ f g → if ⌊ f ♯ᶠⁱⁿ? g ⌋ then just (f ∪ᶠⁱⁿ g) else nothing
  --   .unity {f} →
  --     (begin
  --       ∅ᶠⁱⁿ ∪ᶠⁱⁿ f
  --     ≈⟨ ε-identityˡ f ⟩
  --       f
  --     ∎) ,
  --     (begin
  --       (if ⌊ f ♯ᶠⁱⁿ? ∅ᶠⁱⁿ ⌋ then just (f ∪ᶠⁱⁿ ∅ᶠⁱⁿ) else nothing)
  --     ≈⟨ {!!} ⟩
  --       (if true then just (f ∪ᶠⁱⁿ ∅ᶠⁱⁿ) else nothing)
  --     ≡⟨⟩
  --       just (f ∪ᶠⁱⁿ ∅ᶠⁱⁿ)
  --     ≈⟨ ε-identityʳ f ⟩
  --       just f
  --     ∎)
  --   .associativity → {!!}
  --   .commutativity → {!!}
  --   .cancellative → {!!}
