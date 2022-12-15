{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open Binary
open import Prelude.General
open import Prelude.Lift
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Irrelevance

open import Prelude.Ord.Core
open import Prelude.Ord.Dec
open import Prelude.Ord.Irrelevant

module Prelude.Ord.Product where

module _ {A : Type ℓ} {B : Type ℓ′} ⦃ _ : Ord A ⦄ ⦃ _ : Ord B ⦄ where
  _≤×_ _<×_ : Rel (A × B) _
  (a , b) ≤× (a′ , b′) = (a < a′) ⊎ (a ≡ a′ × b ≤ b′)
  (a , b) <× (a′ , b′) = (a < a′) ⊎ (a ≡ a′ × b < b′)

  private pattern ≪_ x = inj₁ x; pattern ≫_ x = inj₂ (refl , x)

  instance
    Ord-× : Ord (A × B)
    Ord-× = record {_≤_ = _≤×_; _<_ = _<×_}

  module _ ⦃ _ : DecEq A ⦄ ⦃ _ : DecOrd A ⦄ ⦃ _ : DecOrd B ⦄ where instance
    DecOrd-× : DecOrd (A × B)
    DecOrd-× = record {}

  module _ ⦃ _ : OrdLaws A ⦄ ⦃ _ : OrdLaws B ⦄ where instance
    OrdLaws-× : OrdLaws (A × B)
    OrdLaws-× = λ where
      .≤-refl → ≫ ≤-refl
      .≤-trans → λ where
        (≪ p) (≪ q) → ≪ <-trans p q
        (≪ p) (≫ q) → ≪ p
        (≫ p) (≪ q) → ≪ q
        (≫ p) (≫ q) → ≫ ≤-trans p q
      .≤-antisym → λ where
        (≪ p) (≪ q) → ⊥-elim $ <-irrefl refl $ <-trans p q
        (≪ p) (≫ _) → ⊥-elim $ <-irrefl refl p
        (≫ _) (≪ q) → ⊥-elim $ <-irrefl refl q
        (≫ p) (≫ q) → cong (_ ,_) (≤-antisym p q )
      .≤-total → ≤×-total
      .<-irrefl refl → λ where
        (≪ p) → <-irrefl refl p
        (≫ p) → <-irrefl refl p
      .<-trans → λ where
        (≪ p) (≪ q) → ≪ <-trans p q
        (≪ p) (≫ q) → ≪ p
        (≫ p) (≪ q) → ≪ q
        (≫ p) (≫ q) → ≫ <-trans p q
      .<-resp₂-≡ → (λ where refl → id) , (λ where refl → id)
      .<-cmp → <×-cmp
      .<⇒≤ → proj₁ ∘ <×⇒≤×∧≢
      .<⇒≢ → proj₂ ∘ <×⇒≤×∧≢
      .≤∧≢⇒< → ≤×∧≢⇒<×
       where
        ≤×-total : Total _≤×_
        ≤×-total (a , b) (a′ , b′)
          with <-cmp a a′
        ... | tri< a< _ _ = inj₁ (≪ a<)
        ... | tri> _ _ <a = inj₂ (≪ <a)
        ... | tri≈ _ refl _
          with <-cmp b b′
        ... | tri< b< _    _  = inj₁ (≫ <⇒≤ b<)
        ... | tri> _  _    <b = inj₂ (≫ <⇒≤ <b)
        ... | tri≈ _  refl _  = ≪  (≫ ≤-refl)

        <×-cmp : Trichotomous _≡_ _<×_
        <×-cmp (a , b) (a′ , b′)
          with <-cmp a a′
        ... | tri< a< a≢ ≮a
            = tri< (≪ a<)
                          (λ where refl → a≢ refl)
                          (λ where (≪ <a) → ≮a <a; (≫ _) → ≮a a<)
        ... | tri> a≮ a≢ <a
            = tri> (λ where (≪ a<) → a≮ a<; (≫ _) → a≮ <a)
                          (λ where refl → a≢ refl)
                          (≪ <a)
        ... | tri≈ a≮ refl ≮a
          with <-cmp b b′
        ... | tri< b< b≢ ≮b
            = tri< (≫ b<) (λ where refl → b≢ refl)
                          (λ where (≪ a<) → a≮ a<; (≫ <b) → ≮b <b)
        ... | tri> b≮ b≢ <b
            = tri> (λ where (≪ a<) → a≮ a<; (≫ b<) → b≮ b<)
                          (λ where refl → b≢ refl) (≫ <b)
        ... | tri≈ b≮ refl ≮b
            = tri≈ (λ where (≪ a<) → a≮ a<; (≫ b<) → b≮ b<)
                          refl
                          (λ where (≪ a<) → a≮ a<; (≫ b<) → b≮ b<)

        <×⇒≤×∧≢ : _<×_ ⇒² _≤×_ ∩² _≢_
        <×⇒≤×∧≢ = λ where
          (≪ p) → (≪ p) , λ where refl → <⇒≢ p refl
          (≫ p) → ≫ <⇒≤ p , λ where refl → <⇒≢ p refl

        ≤×∧≢⇒<× : _≤×_ ∩² _≢_ ⇒² _<×_
        ≤×∧≢⇒<× = λ where
          (≪ p , ¬eq) → ≪ p
          (≫ p , ¬eq) → ≫ ≤∧≢⇒< (p , λ where refl → ¬eq refl)

    ·-<× : ⦃ _ : ·² _<_ {A = A} ⦄ ⦃ _ : ·² _<_ {A = B} ⦄
        → ·² _<×_
    ·-<× .∀≡ (≪ p) (≪ q) rewrite ∀≡ p q = refl
    ·-<× .∀≡ (≪ p) (≫ q) = ⊥-elim $ <-irrefl refl p
    ·-<× .∀≡ (≫ p) (≪ q) = ⊥-elim $ <-irrefl refl q
    ·-<× .∀≡ (≫ p) (≫ q) rewrite ∀≡ p q = refl

    ·-≤× : ⦃ _ : ·² _≤_ {A = A} ⦄ ⦃ _ : ·² _<_ {A = A} ⦄
        → ⦃ _ : ·² _≤_ {A = B} ⦄ ⦃ _ : ·² _<_ {A = B} ⦄
        → ·² _≤×_
    ·-≤× .∀≡ (≪ p) (≪ q) rewrite ∀≡ p q = refl
    ·-≤× .∀≡ (≪ p) (≫ q) = ⊥-elim $ <-irrefl refl p
    ·-≤× .∀≡ (≫ p) (≪ q) = ⊥-elim $ <-irrefl refl q
    ·-≤× .∀≡ (≫ p) (≫ q) rewrite ∀≡ p q = refl

    ·Ord-× : ⦃ ·Ord A ⦄ → ⦃ ·Ord B ⦄ → ·Ord (A × B)
    ·Ord-× = mk·Ord

module _ {A : Type ℓ} {B : Type ℓ′} ⦃ _ : Ord⁺⁺ A ⦄ ⦃ _ : Ord⁺⁺ B ⦄ where instance
  Ord⁺⁺-× : ⦃ DecEq A ⦄ → Ord⁺⁺ (A × B)
  Ord⁺⁺-× = mkOrd⁺⁺
