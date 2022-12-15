{-# OPTIONS --safe #-}
module Prelude.DecEq.Core where

open import Prelude.Init; open SetAsType

private variable A : Type ℓ; B : Type ℓ′

record DecEq (A : Type ℓ) : Type ℓ where
  field _≟_ : Decidable² {A = A} _≡_

  _==_ : A → A → Bool
  x == y = ⌊ x ≟ y ⌋

  _≠_ : A → A → Bool
  x ≠ y = not (x == y)

  infix 4 _≟_ _==_ _≠_

open DecEq ⦃...⦄ public

Irrelevant⇒DecEq : Irrelevant A → DecEq A
Irrelevant⇒DecEq ∀≡ ._≟_ = yes ∘₂ ∀≡

instance
  DecEq-⊤ : DecEq ⊤
  DecEq-⊤ ._≟_ = Unit._≟_

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
