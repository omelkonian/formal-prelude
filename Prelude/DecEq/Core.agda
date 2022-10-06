module Prelude.DecEq.Core where

open import Prelude.Init

private variable A B : Set ℓ

record DecEq (A : Set ℓ) : Set ℓ where
  field _≟_ : Decidable² {A = A} _≡_

  _==_ : A → A → Bool
  x == y = ⌊ x ≟ y ⌋

  _≠_ : A → A → Bool
  x ≠ y = not (x == y)

  infix 4 _≟_ _==_ _≠_

  ≟-refl : ∀ x → (x ≟ x) ≡ yes refl
  ≟-refl x with refl , p ← dec-yes (x ≟ x) refl = p

open DecEq ⦃ ... ⦄ public

instance
  DecEq-⊤ : DecEq ⊤
  DecEq-⊤ ._≟_ = Unit._≟_

  DecEq-Σ : ∀ {B : A → Set} ⦃ _ : DecEq A ⦄ ⦃ _ : ∀ {x} → DecEq (B x) ⦄ → DecEq (Σ A B)
  DecEq-Σ ._≟_ (x , y) (x′ , y′)
    with x ≟ x′
  ... | no ¬p    = no λ{ refl → ¬p refl }
  ... | yes refl
    with y ≟ y′
  ... | no ¬p    = no λ{ refl → ¬p refl }
  ... | yes refl = yes refl

  DecEq-⊎ : ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ → DecEq (A ⊎ B)
  DecEq-⊎ ._≟_ = Sum.≡-dec _≟_ _≟_

  DecEq-Bool : DecEq Bool
  DecEq-Bool ._≟_ = B._≟_

  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ ._≟_ = Nat._≟_

  DecEq-ℤ : DecEq ℤ
  DecEq-ℤ ._≟_ = Integer._≟_

  DecEq-Char : DecEq Char
  DecEq-Char ._≟_ = Ch._≟_

  DecEq-Fin : ∀ {n} → DecEq (Fin n)
  DecEq-Fin ._≟_ = F._≟_

  DecEq-String : DecEq String
  DecEq-String ._≟_ = Str._≟_

  DecEq-List : ⦃ _ : DecEq A ⦄ → DecEq (List A)
  DecEq-List ._≟_ = L.≡-dec _≟_

  DecEq-List⁺ : ⦃ _ : DecEq A ⦄ → DecEq (List⁺ A)
  DecEq-List⁺ ._≟_ (x ∷ xs) (y ∷ ys)
    with x ≟ y
  ... | no x≢y = no λ{ refl → x≢y refl }
  ... | yes refl
    with xs ≟ ys
  ... | no xs≢ys = no λ{ refl → xs≢ys refl }
  ... | yes refl = yes refl

  DecEq-Vec : ⦃ _ : DecEq A ⦄ → ∀ {n} → DecEq (Vec A n)
  DecEq-Vec ._≟_ = V.≡-dec _≟_

  DecEq-Maybe : ⦃ _ : DecEq A ⦄ → DecEq (Maybe A)
  DecEq-Maybe ._≟_ = M.≡-dec _≟_

  DecEq-These : ⦃ DecEq A ⦄ → ⦃ DecEq B ⦄ → DecEq (These A B)
  DecEq-These ._≟_ = ∣These∣.≡-dec _≟_ _≟_

  -- ** reflection
  open Meta

  DecEq-Name : DecEq Name
  DecEq-Name ._≟_ = RName._≟_
    where import Reflection.Name as RName

  DecEq-Term : DecEq Term
  DecEq-Term ._≟_ = RTerm._≟_
    where import Reflection.Term as RTerm

  DecEq-Arg : ⦃ _ : DecEq A ⦄ → DecEq (Arg A)
  DecEq-Arg ._≟_ = RArg.≡-dec _≟_
    where import Reflection.Argument as RArg

  -- open Visibility
  DecEq-Vis : DecEq Visibility
  DecEq-Vis ._≟_ = RVis._≟_
    where import Reflection.Argument.Visibility as RVis
