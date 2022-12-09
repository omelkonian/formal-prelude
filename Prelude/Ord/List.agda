open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Lift
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Irrelevance

open import Prelude.Ord.Core
open import Prelude.Ord.Dec

module Prelude.Ord.List {A : Type ℓ} where

module _ (_<_ : Rel A ℓ) where
  <∗-from-< : Rel (List A) ℓ
  <∗-from-< = _<∗_ where _<∗_ = λ where
    [] [] → ↑ℓ ⊥
    [] (_ ∷ _) → ↑ℓ ⊤
    (_ ∷ _) [] → ↑ℓ ⊥
    (x ∷ xs) (y ∷ ys) → (x < y) ⊎ ((x ≡ y) × (xs <∗ ys))

  <∗?-from-<? : ⦃ _ : DecEq A ⦄ → Decidable² _<_ → Decidable² <∗-from-<
  <∗?-from-<? _<?_ = _<∗?_ where _<∗?_ = λ where
    [] [] → no λ ()
    [] (_ ∷ _) → yes it
    (_ ∷ _) [] → no λ ()
    (x ∷ xs) (y ∷ ys) → (x <? y) ⊎-dec ((x ≟ y) ×-dec (xs <∗? ys))

module _ ⦃ _ : Ord A ⦄ where
  _<∗_ = Rel (List A) ℓ ∋ <∗-from-< _<_
  pattern <∗ˡ_ x = inj₁ x
  pattern <∗ʳ_ x = inj₂ (refl , x)

  _≤∗_ = Rel (List A) ℓ ∋ ≤-from-< _<∗_
  pattern ≤∗ˡ = inj₁ refl
  pattern ≤∗ʳ_ x = inj₂ x

  instance Ord-List = Ord (List A) ∋ mkOrd< _<∗_

module _ ⦃ _ : Ord A ⦄ ⦃ _ : DecEq A ⦄ ⦃ _ : DecOrd A ⦄ where

  _<∗?_ : Decidable² _<∗_
  _<∗?_ = <∗?-from-<? _<_ _<?_

  instance
    Dec-<∗ : _<∗_ ⁇²
    Dec-<∗ .dec = _ <∗? _

    DecOrd-List : DecOrd (List A)
    DecOrd-List = record {}

module _ ⦃ _ : Ord A ⦄ ⦃ _ : OrdLaws A ⦄ where instance

  postulate OrdLaws-List : OrdLaws (List A)

  ·-<∗ : ⦃ _ : ·² _<_ {A = A} ⦄ → ·² _<∗_
  ·-<∗ {x = xs} {ys} .∀≡ = go xs ys
    where
      go : ∀ (xs ys : List A) → Irrelevant (xs <∗ ys)
      go = λ where
        []      (_ ∷ _) (lift tt) (lift tt) → refl
        (_ ∷ _) (_ ∷ _) (<∗ˡ _)   (<∗ˡ _)   → cong <∗ˡ_ (∀≡ _ _)
        (_ ∷ _) (_ ∷ _) (<∗ˡ p)   (<∗ʳ _)   → ⊥-elim $ <-irrefl refl p
        (_ ∷ _) (_ ∷ _) (<∗ʳ _)   (<∗ˡ q)   → ⊥-elim $ <-irrefl refl q
        (_ ∷ _) (_ ∷ _) (<∗ʳ _)   (<∗ʳ _)   → cong <∗ʳ_ (∀≡ _ _)

  ·-≤∗ : ⦃ _ : ·² _≤_ {A = A} ⦄ ⦃ _ : ·² _<_ {A = A} ⦄ → ·² _≤∗_
  ·-≤∗ .∀≡ = λ where
    ≤∗ˡ     ≤∗ˡ     → refl
    ≤∗ˡ     (≤∗ʳ q) → ⊥-elim $ <-irrefl refl q
    (≤∗ʳ p) ≤∗ˡ     → ⊥-elim $ <-irrefl refl p
    (≤∗ʳ _) (≤∗ʳ _) → cong ≤∗ʳ_ (∀≡ _ _)
