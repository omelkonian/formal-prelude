module Prelude.Ord.Product where

open import Prelude.Init; open SetAsType
open Binary
open import Prelude.General
open import Prelude.Lift
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Irrelevance

open import Prelude.Ord.Core

private variable A : Type ℓ; B : Type ℓ′

module _ ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : Ord A ⦄ ⦃ _ : Ord B ⦄ where
  private
    _≤×_ : Rel (A × B) _
    (a , b) ≤× (a′ , b′) = (a < a′) ⊎ (a ≡ a′ × b ≤ b′)
    pattern ≤×ˡ_ x = inj₁ x
    pattern ≤×ʳ_ x = inj₂ (refl , x)

    _<×_ : Rel (A × B) _
    (a , b) <× (a′ , b′) = (a < a′) ⊎ (a ≡ a′ × b < b′)
    pattern <×ˡ_ x = inj₁ x
    pattern <×ʳ_ x = inj₂ (refl , x)

  instance
    Ord-× : Ord (A × B)
    Ord-× = record {_≤_ = _≤×_; _<_ = _<×_}

    OrdLaws-× : ⦃ OrdLaws A ⦄ → ⦃ OrdLaws B ⦄ → OrdLaws (A × B)
    OrdLaws-× = λ where
      .≤-refl → ≤×ʳ ≤-refl
      .≤-trans → λ where
        (≤×ˡ p) (≤×ˡ q) → ≤×ˡ <-trans p q
        (≤×ˡ p) (≤×ʳ q) → ≤×ˡ p
        (≤×ʳ p) (≤×ˡ q) → ≤×ˡ q
        (≤×ʳ p) (≤×ʳ q) → ≤×ʳ ≤-trans p q
      .≤-antisym → λ where
        (≤×ˡ p) (≤×ˡ q) → ⊥-elim $ <-irrefl refl $ <-trans p q
        (≤×ˡ p) (≤×ʳ _) → ⊥-elim $ <-irrefl refl p
        (≤×ʳ _) (≤×ˡ q) → ⊥-elim $ <-irrefl refl q
        (≤×ʳ p) (≤×ʳ q) → cong (_ ,_) (≤-antisym p q )
      .≤-total → ≤×-total
      .<-irrefl refl → λ where
        (<×ˡ p) → <-irrefl refl p
        (<×ʳ p) → <-irrefl refl p
      .<-trans → λ where
        (<×ˡ p) (<×ˡ q) → <×ˡ <-trans p q
        (<×ˡ p) (<×ʳ q) → <×ˡ p
        (<×ʳ p) (<×ˡ q) → <×ˡ q
        (<×ʳ p) (<×ʳ q) → <×ʳ <-trans p q
      .<-resp₂-≡ → (λ where refl → id) , (λ where refl → id)
      .<-cmp → <×-cmp
      .<⇒≤ → proj₁ ∘ <×⇒≤×∧≢
      .<⇒≢ → proj₂ ∘ <×⇒≤×∧≢
      .≤∧≢⇒< → ≤×∧≢⇒<×
     where
        ≤×-total : Total _≤×_
        ≤×-total (a , b) (a′ , b′)
          with <-cmp a a′
        ... | tri< a< _ _ = inj₁ (≤×ˡ a<)
        ... | tri> _ _ <a = inj₂ (≤×ˡ <a)
        ... | tri≈ _ refl _
          with <-cmp b b′
        ... | tri< b< _    _  = inj₁ (≤×ʳ <⇒≤ b<)
        ... | tri> _  _    <b = inj₂ (≤×ʳ <⇒≤ <b)
        ... | tri≈ _  refl _  = <×ˡ  (≤×ʳ ≤-refl)

        <×-cmp : Trichotomous _≡_ _<×_
        <×-cmp (a , b) (a′ , b′)
          with <-cmp a a′
        ... | tri< a< a≢ ≮a
            = tri< (<×ˡ a<)
                          (λ where refl → a≢ refl)
                          (λ where (<×ˡ <a) → ≮a <a; (<×ʳ _) → ≮a a<)
        ... | tri> a≮ a≢ <a
            = tri> (λ where (<×ˡ a<) → a≮ a<; (<×ʳ _) → a≮ <a)
                          (λ where refl → a≢ refl)
                          (<×ˡ <a)
        ... | tri≈ a≮ refl ≮a
          with <-cmp b b′
        ... | tri< b< b≢ ≮b
            = tri< (<×ʳ b<) (λ where refl → b≢ refl)
                          (λ where (<×ˡ a<) → a≮ a<; (<×ʳ <b) → ≮b <b)
        ... | tri> b≮ b≢ <b
            = tri> (λ where (<×ˡ a<) → a≮ a<; (<×ʳ b<) → b≮ b<)
                          (λ where refl → b≢ refl) (<×ʳ <b)
        ... | tri≈ b≮ refl ≮b
            = tri≈ (λ where (<×ˡ a<) → a≮ a<; (<×ʳ b<) → b≮ b<)
                          refl
                          (λ where (<×ˡ a<) → a≮ a<; (<×ʳ b<) → b≮ b<)

        <×⇒≤×∧≢ : _<×_ ⇒² _≤×_ ∩² _≢_
        <×⇒≤×∧≢ = λ where
          (<×ˡ p) → (≤×ˡ p) , λ where refl → <⇒≢ p refl
          (<×ʳ p) → ≤×ʳ <⇒≤ p , λ where refl → <⇒≢ p refl

        ≤×∧≢⇒<× : _≤×_ ∩² _≢_ ⇒² _<×_
        ≤×∧≢⇒<× = λ where
          (≤×ˡ p , ¬eq) → <×ˡ p
          (≤×ʳ p , ¬eq) → ≤×ʳ ≤∧≢⇒< (p , λ where refl → ¬eq refl)

    ·-<× : ⦃ _ : OrdLaws A ⦄ ⦃ _ : OrdLaws B ⦄
        → ⦃ _ : ·² _<_ {A = A} ⦄ ⦃ _ : ·² _<_ {A = B} ⦄
        → ·² _<×_
    ·-<× .∀≡ (<×ˡ p) (<×ˡ q) rewrite ∀≡ p q = refl
    ·-<× .∀≡ (<×ˡ p) (<×ʳ q) = ⊥-elim $ <-irrefl refl p
    ·-<× .∀≡ (<×ʳ p) (<×ˡ q) = ⊥-elim $ <-irrefl refl q
    ·-<× .∀≡ (<×ʳ p) (<×ʳ q) rewrite ∀≡ p q = refl

    ·-≤× : ⦃ _ : OrdLaws A ⦄ ⦃ _ : OrdLaws B ⦄
        → ⦃ _ : ·² _≤_ {A = A} ⦄ ⦃ _ : ·² _<_ {A = A} ⦄
        → ⦃ _ : ·² _≤_ {A = B} ⦄ ⦃ _ : ·² _<_ {A = B} ⦄
        → ·² _≤×_
    ·-≤× .∀≡ (≤×ˡ p) (≤×ˡ q) rewrite ∀≡ p q = refl
    ·-≤× .∀≡ (≤×ˡ p) (≤×ʳ q) = ⊥-elim $ <-irrefl refl p
    ·-≤× .∀≡ (≤×ʳ p) (≤×ˡ q) = ⊥-elim $ <-irrefl refl q
    ·-≤× .∀≡ (≤×ʳ p) (≤×ʳ q) rewrite ∀≡ p q = refl
