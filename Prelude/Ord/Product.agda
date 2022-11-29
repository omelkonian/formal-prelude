open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Lift
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Irrelevance

open import Prelude.Orders
open import Prelude.Ord.Core

module Prelude.Ord.Product {A : Type ℓ} {B : Type ℓ′} ⦃ _ : Ord A ⦄ ⦃ _ : Ord B ⦄ where

_≤×_ : Rel (A × B) _
(a , b) ≤× (a′ , b′) = (a < a′) ⊎ (a ≡ a′ × b ≤ b′)
pattern ≤×ˡ_ x = inj₁ x
pattern ≤×ʳ_ x = inj₂ (refl , x)

_<×_ : Rel (A × B) _
(a , b) <× (a′ , b′) = (a < a′) ⊎ (a ≡ a′ × b < b′)
pattern <×ˡ_ x = inj₁ x
pattern <×ʳ_ x = inj₂ (refl , x)

-- T0D0: cannot declare these as instances without breaking instance resolution.
module Product-Ord where
-- instance
  Ord-× : Ord (A × B)
  Ord-× = λ where
    .relℓ → _
    ._≤_  → _≤×_
    ._<_  → _<×_

  ≤×-to-<× : ⦃ _ : NonStrictToStrict {A = A} _≤_ _<_ ⦄
           → ⦃ _ : NonStrictToStrict {A = B} _≤_ _<_ ⦄
           → NonStrictToStrict _≤×_ _<×_
  ≤×-to-<× .<⇔≤∧≢ = ↝ , ↜
    where
      ↝ : _<×_ ⇒² _≤×_ ∩² _≢_
      ↝ (<×ˡ p) = (≤×ˡ p) , λ where refl → <⇒≢ p refl
      ↝ (<×ʳ p) = ≤×ʳ <⇒≤ p , λ where refl → <⇒≢ p refl

      ↜ : _≤×_ ∩² _≢_ ⇒² _<×_
      ↜ (≤×ˡ p , ¬eq) = <×ˡ p
      ↜ (≤×ʳ p , ¬eq) = ≤×ʳ ≤∧≢⇒< (p , λ where refl → ¬eq refl)

  module _
    ⦃ _ : TotalOrder $ _≤_ {A = A} ⦄
    ⦃ _ : StrictTotalOrder $ _<_ {A = A} ⦄
    ⦃ _ : NonStrictToStrict {A = A} _≤_ _<_ ⦄

    ⦃ _ : TotalOrder $ _≤_ {A = B} ⦄
    ⦃ _ : StrictTotalOrder $ _<_ {A = B} ⦄
    ⦃ _ : NonStrictToStrict {A = B} _≤_ _<_ ⦄
    where
    instance
      Preorder-≤× : Preorder _≤×_
      Preorder-≤× = λ where
        .≤-refl → ≤×ʳ ≤-refl
        .≤-trans → λ where
          (≤×ˡ p) (≤×ˡ q) → ≤×ˡ <-trans p q
          (≤×ˡ p) (≤×ʳ q) → ≤×ˡ p
          (≤×ʳ p) (≤×ˡ q) → ≤×ˡ q
          (≤×ʳ p) (≤×ʳ q) → ≤×ʳ ≤-trans p q

      PartialOrder-≤× : PartialOrder _≤×_
      PartialOrder-≤× .≤-antisym = λ where
        (≤×ˡ p) (≤×ˡ q) → ⊥-elim $ <-irrefl refl $ <-trans p q
        (≤×ˡ p) (≤×ʳ _) → ⊥-elim $ <-irrefl refl p
        (≤×ʳ _) (≤×ˡ q) → ⊥-elim $ <-irrefl refl q
        (≤×ʳ p) (≤×ʳ q) → cong (_ ,_) (≤-antisym p q )

      TotalOrder-≤× : TotalOrder _≤×_
      TotalOrder-≤× .≤-total (a , b) (a′ , b′)
        with <-cmp a a′
      ... | Binary.tri< a< _ _ = inj₁ (≤×ˡ a<)
      ... | Binary.tri> _ _ <a = inj₂ (≤×ˡ <a)
      ... | Binary.tri≈ _ refl _
        with <-cmp b b′
      ... | Binary.tri< b< _    _  = inj₁ (≤×ʳ <⇒≤ b<)
      ... | Binary.tri> _  _    <b = inj₂ (≤×ʳ <⇒≤ <b)
      ... | Binary.tri≈ _  refl _  = <×ˡ  (≤×ʳ ≤-refl)


      StrictPartialOrder-<× : StrictPartialOrder _<×_
      StrictPartialOrder-<× = λ where
        .<-irrefl refl → λ where
          (<×ˡ p) → <-irrefl refl p
          (<×ʳ p) → <-irrefl refl p
        .<-trans → λ where
          (<×ˡ p) (<×ˡ q) → <×ˡ <-trans p q
          (<×ˡ p) (<×ʳ q) → <×ˡ p
          (<×ʳ p) (<×ˡ q) → <×ˡ q
          (<×ʳ p) (<×ʳ q) → <×ʳ <-trans p q
        .<-resp₂-≡ → (λ where refl → id) , (λ where refl → id)

      StrictTotalOrder-<× : StrictTotalOrder _<×_
      StrictTotalOrder-<× .<-cmp (a , b) (a′ , b′)
        with <-cmp a a′
      ... | Binary.tri< a< a≢ ≮a
          = Binary.tri< (<×ˡ a<)
                        (λ where refl → a≢ refl)
                        (λ where (<×ˡ <a) → ≮a <a; (<×ʳ _) → ≮a a<)
      ... | Binary.tri> a≮ a≢ <a
          = Binary.tri> (λ where (<×ˡ a<) → a≮ a<; (<×ʳ _) → a≮ <a)
                        (λ where refl → a≢ refl)
                        (<×ˡ <a)
      ... | Binary.tri≈ a≮ refl ≮a
        with <-cmp b b′
      ... | Binary.tri< b< b≢ ≮b
          = Binary.tri< (<×ʳ b<) (λ where refl → b≢ refl)
                        (λ where (<×ˡ a<) → a≮ a<; (<×ʳ <b) → ≮b <b)
      ... | Binary.tri> b≮ b≢ <b
          = Binary.tri> (λ where (<×ˡ a<) → a≮ a<; (<×ʳ b<) → b≮ b<)
                        (λ where refl → b≢ refl) (<×ʳ <b)
      ... | Binary.tri≈ b≮ refl ≮b
          = Binary.tri≈ (λ where (<×ˡ a<) → a≮ a<; (<×ʳ b<) → b≮ b<)
                        refl
                        (λ where (<×ˡ a<) → a≮ a<; (<×ʳ b<) → b≮ b<)

      -- ·-<× : ⦃ _ : ·² _<_ {A = A} ⦄
      --      → ⦃ _ : ·² _<_ {A = B} ⦄
      --      → ·² _<×_
      -- ·-<× .∀≡ (<×ˡ p) (<×ˡ q) rewrite ∀≡ p q = refl
      -- ·-<× .∀≡ (<×ˡ p) (<×ʳ q) = ⊥-elim $ <-irrefl refl p
      -- ·-<× .∀≡ (<×ʳ p) (<×ˡ q) = ⊥-elim $ <-irrefl refl q
      -- ·-<× .∀≡ (<×ʳ p) (<×ʳ q) rewrite ∀≡ p q = refl

      ·-≤× : ⦃ _ : ·² _≤_ {A = A} ⦄ ⦃ _ : ·² _<_ {A = A} ⦄
           → ⦃ _ : ·² _≤_ {A = B} ⦄ ⦃ _ : ·² _<_ {A = B} ⦄
           → ·² _≤×_
      ·-≤× .∀≡ (≤×ˡ p) (≤×ˡ q) rewrite ∀≡ p q = refl
      ·-≤× .∀≡ (≤×ˡ p) (≤×ʳ q) = ⊥-elim $ <-irrefl refl p
      ·-≤× .∀≡ (≤×ʳ p) (≤×ˡ q) = ⊥-elim $ <-irrefl refl q
      ·-≤× .∀≡ (≤×ʳ p) (≤×ʳ q) rewrite ∀≡ p q = refl
