module Prelude.Ord.List where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Lift
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Irrelevance

open import Prelude.Ord.Core
open import Prelude.Ord.Dec
open import Prelude.Ord.Irrelevant

module _ {A : Type ℓ} ⦃ _ : Ord A ⦄ where

  private
    pattern ≪_ x = inj₁ x; pattern ≫_ x = inj₂ x
    pattern ≪≡ = ≪ refl;   pattern ≫≡_ x = ≫ (refl , x)

  _<∗_ _≤∗_ : Rel (List A) ℓ
  _<∗_ = λ where
    [] [] → ↑ℓ ⊥
    [] (_ ∷ _) → ↑ℓ ⊤
    (_ ∷ _) [] → ↑ℓ ⊥
    (x ∷ xs) (y ∷ ys) → (x < y) ⊎ ((x ≡ y) × (xs <∗ ys))
  _≤∗_ = ≤-from-< _<∗_

  instance
    Ord-List : Ord (List A)
    Ord-List = mkOrd< _<∗_

  module _ ⦃ _ : DecEq A ⦄ ⦃ _ : DecOrd A ⦄ where

    _<∗?_ : Decidable² _<∗_
    _<∗?_ = λ where
      [] [] → no λ ()
      [] (_ ∷ _) → yes it
      (_ ∷ _) [] → no λ ()
      (x ∷ xs) (y ∷ ys) → (x <? y) ⊎-dec ((x ≟ y) ×-dec (xs <∗? ys))

    instance
      Dec-<∗ : _<∗_ ⁇²
      Dec-<∗ .dec = _ <∗? _

      DecOrd-List : DecOrd (List A)
      DecOrd-List = record {}

  module _ ⦃ _ : OrdLaws A ⦄ where instance

    postulate OrdLaws-List : OrdLaws (List A)

    ·-<∗ : ⦃ _ : ·² _<_ {A = A} ⦄ → ·² _<∗_
    ·-<∗ {x = xs} {ys} .∀≡ = go xs ys
      where
        go : ∀ (xs ys : List A) → Irrelevant (xs <∗ ys)
        go = λ where
          []      (_ ∷ _) (lift tt) (lift tt) → refl
          (_ ∷ _) (_ ∷ _) (≪ _)  (≪ _)  → cong ≪_ (∀≡ _ _)
          (_ ∷ _) (_ ∷ _) (≪ p)  (≫≡ _) → ⊥-elim $ <-irrefl refl p
          (_ ∷ _) (_ ∷ _) (≫≡ _) (≪ q)  → ⊥-elim $ <-irrefl refl q
          (_ ∷ _) (_ ∷ _) (≫≡ _) (≫≡ _) → cong ≫≡_ (∀≡ _ _)

    ·-≤∗ : ⦃ _ : ·² _≤_ {A = A} ⦄ ⦃ _ : ·² _<_ {A = A} ⦄ → ·² _≤∗_
    ·-≤∗ .∀≡ = λ where
      ≪≡    ≪≡    → refl
      ≪≡    (≫ q) → ⊥-elim $ <-irrefl refl q
      (≫ p) ≪≡    → ⊥-elim $ <-irrefl refl p
      (≫ _) (≫ _) → cong ≫_ (∀≡ _ _)

    ·Ord-List : ⦃ ·Ord A ⦄ → ·Ord (List A)
    ·Ord-List = mk·Ord

module _ {A : Type ℓ} ⦃ _ : Ord⁺⁺ A ⦄ where instance
  Ord⁺⁺-List : ⦃ DecEq A ⦄ → Ord⁺⁺ (List A)
  Ord⁺⁺-List = mkOrd⁺⁺
