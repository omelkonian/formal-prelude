{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Setoid
open import Prelude.Apartness

open import Prelude.Sets.AsUniqueLists.Core
open import Prelude.Sets.AsUniqueLists.SetMappings

module Prelude.Sets.AsUniqueLists.SetMappings2 {A : Type} ⦃ _ : DecEq A ⦄ where

private variable
  x x′ : A; xs xs′ ys zs : Set⟨ A ⟩
  B : Type; P : Pred₀ A

_→ᶠⁱⁿ_ : (A : Type) ⦃ _ : DecEq A ⦄ → Type → Type
A →ᶠⁱⁿ B = Σ Set⟨ A ⟩ (_↦ B)

SemigroupLaws≈ : (A : Type ℓ) ⦃ _ : Semigroup A ⦄ ⦃ _ : ISetoid A ⦄ → Type _
SemigroupLaws≈ A = SemigroupLaws A _≈_

MonoidLaws≈ : (A : Type ℓ) ⦃ _ : Monoid A ⦄ ⦃ _ : ISetoid A ⦄ → Type _
MonoidLaws≈ A = MonoidLaws A _≈_

instance
  Semigroup-↦ : Semigroup (A →ᶠⁱⁿ B)
  Semigroup-↦ ._◇_ (xs , f) (ys , g) = xs ∪ ys , f ∪/↦ g

  Monoid-↦ : Monoid (A →ᶠⁱⁿ B)
  Monoid-↦ .ε = ∅ , (mk↦ ⊥-elim ∘ ∉∅ _)


open ≈-Reasoning

module _ ⦃ _ : ISetoid B ⦄ where
  instance
    //-↦ : (A →ᶠⁱⁿ B) // (A →ᶠⁱⁿ B)
    //-↦ = λ where ._♯_ → _♯_ on proj₁

    -- Dec-//-↦ : _♯_ {A = A →ᶠⁱⁿ B} ⁇²
    -- Dec-//-↦ {f}{g} .dec = f .proj₁ ♯ˢ? g .proj₁

    Setoid-↦ :  ISetoid (A →ᶠⁱⁿ B)
    Setoid-↦ = λ where
      .relℓ → _
      ._≈_ (xs , mk↦_ f) (ys , mk↦_ g) →
        ∃ λ (xs≈ : xs ≈ ys) →
          ∀ x → (x∈ : x ∈ˢ xs) → f x∈ ≈ g (xs≈ .proj₁ x∈)

    SetoidLaws-↦ : SetoidLaws (A →ᶠⁱⁿ B)
    SetoidLaws-↦ = {!!}

    SemigroupLaws-↦ : SemigroupLaws≈ (A →ᶠⁱⁿ B)
    SemigroupLaws-↦ = record { ◇-comm = {!!} ; ◇-assocʳ = {!!} }

    MonoidLaws-↦ : MonoidLaws≈ (A →ᶠⁱⁿ B)
    MonoidLaws-↦ .ε-identity
      = (λ f → {!∪-∅ˡ (f .proj₁)!})
      , (λ f → {!!})


  _♯↦_ = Rel₀ (A →ᶠⁱⁿ B) ∋ _♯_

  _♯↦?_ : Decidable² _♯↦_
  f ♯↦? g = f .proj₁ ♯ˢ? g .proj₁
