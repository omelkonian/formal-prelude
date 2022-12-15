{-# OPTIONS --with-K #-}
-- {-# OPTIONS --safe #-}
open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Lift
open import Prelude.DecEq.Core
open import Prelude.Decidable
open import Prelude.Irrelevance.Core
open import Prelude.Irrelevance.WithK

open import Prelude.Ord.Core
open import Prelude.Ord.Dec
open import Prelude.Ord.Irrelevant

module Prelude.Ord.Sum where

open Binary
private pattern ≪_ x = inj₁ x; pattern ≫_ x = inj₂ x; pattern ≪≡ = ≪ refl

module _ {A : Type ℓ} {B : Type ℓ′} ⦃ _ : Ord A ⦄ ⦃ _ : Ord B ⦄ where
  _≤⊎_ _<⊎_ : Rel (A ⊎ B) (ℓ ⊔ₗ ℓ′)
  _≤⊎_ = ≤-from-< _<⊎_
  _<⊎_ = λ where
    (≪ x) (≪ y) → ↑ℓ (x < y) {ℓ′}
    (≪ _) (≫ _) → ↑ℓ ⊤
    (≫ _) (≪ _) → ↑ℓ ⊥
    (≫ x) (≫ y) → ↑ℓ (x < y) {ℓ}

  instance
    Ord-⊎ : Ord (A ⊎ B)
    Ord-⊎ = mkOrd< _<⊎_

  module _ ⦃ _ : DecOrd A ⦄ ⦃ _ : DecOrd B ⦄ where
    _<⊎?_ : Decidable² _<⊎_
    _<⊎?_ = λ where
      (≪ x) (≪ y) → ↑ℓ-dec (x <? y)
      (≪ _) (≫ _) → yes it
      (≫ _) (≪ _) → no λ ()
      (≫ x) (≫ y) → ↑ℓ-dec (x <? y)

    instance
      Dec<-⊎ : _<⊎_ ⁇²
      Dec<-⊎ .dec = _ <⊎? _

      DecOrd-× : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → DecOrd (A ⊎ B)
      DecOrd-× = record {}

  module _ ⦃ _ : OrdLaws A ⦄ ⦃ _ : OrdLaws B ⦄ where instance
    {-# TERMINATING #-}
    OrdLaws-⊎ : OrdLaws (A ⊎ B)
    OrdLaws-⊎ = λ where
      .≤-refl → ≪≡
      .≤-trans → λ where
        ≪≡ ≪≡ → ≪≡
        ≪≡ (≫ q) → ≫ q
        (≫ p) ≪≡ → ≫ p
        (≫ p) (≫ q) → ≫ <-trans p q
      .≤-antisym → λ where
        ≪≡ ≪≡ → refl
        ≪≡ (≫ _) → refl
        (≫ _) ≪≡ → refl
        (≫ p) (≫ q) → ⊥-elim $ <-irrefl refl (<-trans p q)
      .≤-total (≪ x) (≪ y) → case <-cmp x y of λ where
        (tri< x<y _ _) → ≪ ≫ lift x<y
        (tri≈ _ refl _) → ≪ ≪≡
        (tri> _ _ y<x) → ≫ ≫ lift y<x
      .≤-total (≪ x) (≫ y) → ≪ ≫ it
      .≤-total (≫ x) (≪ y) → ≫ ≫ it
      .≤-total (≫ x) (≫ y) → case <-cmp x y of λ where
        (tri< x<y _ _) → ≪ ≫ lift x<y
        (tri≈ _ refl _) → ≪ ≪≡
        (tri> _ _ y<x) → ≫ ≫ lift y<x
      .<-irrefl {≪ _} refl → <-irrefl refl ∘ lower
      .<-irrefl {≫ _} refl → <-irrefl refl ∘ lower
      .<-trans {≪ x} {≪ y} {≪ z} (lift p) (lift q) → lift $ <-trans p q
      .<-trans {≪ x} {≪ y} {≫ z} (lift p) q → it
      .<-trans {≪ x} {≫ y} {≫ z} p q → it
      .<-trans {≫ x} {≫ y} {≫ z} (lift p) (lift q) → lift $ <-trans p q
      .<-resp₂-≡ → (λ where refl → id) , (λ where refl → id)
      .<-cmp (≪ x) (≪ y) → Tri-map (lift , lower) ((λ where refl → refl) , (λ where refl → refl)) (lift , lower) (<-cmp x y)
      .<-cmp (≪ x) (≫ y) → tri< it    (λ ()) lower
      .<-cmp (≫ x) (≪ y) → tri> lower (λ ()) it
      .<-cmp (≫ x) (≫ y) → Tri-map (lift , lower) ((λ where refl → refl) , (λ where refl → refl)) (lift , lower) (<-cmp x y)
      .<⇒≤ → inj₂
      .<⇒≢ {≪ x} {≪ .x} (lift p) refl → <-irrefl refl p
      .<⇒≢ {≫ x} {≫ .x} (lift p) refl → <-irrefl refl p
      .≤∧≢⇒< (≪≡ , x≢x) → ⊥-elim $ x≢x refl
      .≤∧≢⇒< ((≫ p) , _) → p

    ·-<⊎ : ⦃ _ : ·² _<_ {A = A} ⦄ ⦃ _ : ·² _<_ {A = B} ⦄
          → ·² _<⊎_
    ·-<⊎ {≪ _} {≪ _} .∀≡ (lift p)  (lift q)  rewrite ∀≡ p q = refl
    ·-<⊎ {≪ _} {≫ _} .∀≡ (lift tt) (lift tt) = refl
    ·-<⊎ {≫ _} {≫ _} .∀≡ (lift p)  (lift q)  rewrite ∀≡ p q = refl

    ·-≤⊎ : ⦃ _ : ·² _≤_ {A = A} ⦄ ⦃ _ : ·² _<_ {A = A} ⦄
          → ⦃ _ : ·² _≤_ {A = B} ⦄ ⦃ _ : ·² _<_ {A = B} ⦄
          → ·² _≤⊎_
    ·-≤⊎ .∀≡ (≪ p) (≪ q) rewrite ∀≡ p q = refl
    ·-≤⊎ .∀≡ ≪≡    (≫ q) = ⊥-elim $ <-irrefl refl q
    ·-≤⊎ .∀≡ (≫ p) ≪≡    = ⊥-elim $ <-irrefl refl p
    ·-≤⊎ .∀≡ (≫ p) (≫ q) rewrite ∀≡ p q = refl

    ·Ord-⊎ : ⦃ ·Ord A ⦄ → ⦃ ·Ord B ⦄ → ·Ord (A ⊎ B)
    ·Ord-⊎ = mk·Ord

module _ {A : Type ℓ} {B : Type ℓ′} ⦃ _ : Ord⁺⁺ A ⦄ ⦃ _ : Ord⁺⁺ B ⦄ where instance
  Ord⁺⁺-⊎ : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → Ord⁺⁺ (A ⊎ B)
  Ord⁺⁺-⊎ = mkOrd⁺⁺
