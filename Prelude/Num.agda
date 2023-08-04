{-# OPTIONS --safe #-}
module Prelude.Num where

open import Prelude.Init; open SetAsType
open import Prelude.FromN
open import Prelude.Decidable
open import Prelude.Newtype
open import Prelude.Membership
open import Prelude.Lists.Indexed

record Num (A : Type ℓ) : Type (lsuc ℓ) where
  field
    Constraint : Pred ℕ ℓ
    fromNum    : (n : ℕ) → ⦃ Constraint n ⦄ → A
open Num ⦃...⦄ public using (fromNum)
{-# BUILTIN FROMNAT fromNum #-}
{-# DISPLAY Num.fromNum _ n = fromNum n #-}

record FromNeg (A : Type ℓ) : Type (lsuc ℓ) where
  field
    Constraint : Pred ℕ ℓ
    fromNeg    : (n : ℕ) → ⦃ Constraint n ⦄ → A
open FromNeg ⦃...⦄ public using (fromNeg)
{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY FromNeg.fromNeg _ n = fromNeg n #-}

open Num using (Constraint)

private variable A : Set; x : A; xs : List A

-- instance
Fromℕ⇒Num : ⦃ Fromℕ A ⦄ → Num A
Fromℕ⇒Num = λ where
  .Constraint _ → ⊤
  .fromNum    n → fromℕ n

instance
  Num-ℕ = Fromℕ⇒Num {A = ℕ}
  Num-ℤ = Fromℕ⇒Num {A = ℤ}
  Num-Char = Fromℕ⇒Num {A = Char}
  Num-∃Fin = Fromℕ⇒Num {A = ∃ Fin}
  Num-Word = Fromℕ⇒Num {A = Word64}
  Num-ℕᵇ = Fromℕ⇒Num {A = ℕᵇ}

  Num-newtype : ⦃ Num A ⦄ → Num (newtype A)
  Num-newtype ⦃ fa ⦄ = λ where
    .Constraint → fa .Constraint
    .fromNum n ⦃ p ⦄ → mk (fromNum n ⦃ p ⦄)

  Num-Fin : ∀ {n} → Num (Fin n)
  Num-Fin {n} = λ where
    .Constraint m         → True (m Nat.<? n)
    .fromNum    m ⦃ m<n ⦄ → F.#_ m {m<n = m<n}

  Num-∈ : {x : A} {xs : List A} → Num (x ∈ xs)
  Num-∈ {x = x} {xs = xs} = λ where
    .Constraint m        → (xs ⁉ m) ≡ just x
    .fromNum    m ⦃ eq ⦄ → just-⁉⇒∈ eq

_ = ℕ         ∋ 42
_ = ℕ         ∋ fromNum 42
_ = newtype ℕ ∋ 42
_ = newtype ℕ ∋ fromNum 42
_ = ℤ         ∋ 42
_ = ℤ         ∋ fromNum 42
_ = Char      ∋ 42
_ = Char      ∋ fromNum 42
_ = Word64    ∋ 42
_ = Word64    ∋ fromNum 42
_ = ℕᵇ        ∋ 42
_ = ℕᵇ        ∋ fromNum 42

_ = Fin 5 ∋ 3

private ns = List ℕ ∋ [ 0 ⨾ 1 ⨾ 2 ⨾ 3 ⨾ 4 ⨾ 5 ]

_ = 0 ≡ (Index ns ∋ 0F) ∋ refl
_ = 5 ≡ (Index ns ∋ 5F) ∋ refl

_ = (ns ‼ 0) ≡ (ns ‼ 0F) ∋ refl
_ = (ns ‼ 5) ≡ (ns ‼ 5F) ∋ refl

_ = 0 ∈ ns ∋ 0
_ = 1 ∈ ns ∋ 1
_ = 2 ∈ ns ∋ 2
_ = 3 ∈ ns ∋ 3
_ = 4 ∈ ns ∋ 4
_ = 5 ∈ ns ∋ 5

open import Data.Rational.Base using (ℚ)

instance
  FromNeg-ℤ : FromNeg ℤ
  FromNeg-ℤ = λ where
    .FromNeg.Constraint _ → ⊤
    .fromNeg n → Integer.- (+ n)

  FromNeg-ℚ : FromNeg ℚ
  FromNeg-ℚ = λ where
    .FromNeg.Constraint _ → ⊤
    .fromNeg n → fromℤ (fromNeg n)
   where
    import Data.Nat.Coprimality as Co

    fromℤ : ℤ → ℚ
    fromℤ z = record
      { numerator     = z
      ; denominator-1 = zero
      ; isCoprime     = Co.sym (Co.1-coprimeTo Integer.∣ z ∣)
      }

  FromNeg-∈ : {x : A} {xs : List A} → FromNeg (x ∈ xs)
  FromNeg-∈ {x = x} {xs = xs} = λ where
    .FromNeg.Constraint m        → (xs ⁉ length xs ∸ m) ≡ just x
    .fromNeg            m ⦃ eq ⦄ → just-⁉⇒∈ eq


_ = ℤ ∋ -42
_ = ℚ ∋ -42

_ = 0 ∈ ns ∋ -0
_ = 5 ∈ ns ∋ -1
_ = 4 ∈ ns ∋ -2
_ = 3 ∈ ns ∋ -3
_ = 2 ∈ ns ∋ -4
_ = 1 ∈ ns ∋ -5
_ = 0 ∈ ns ∋ -6
_ = 0 ∈ ns ∋ -7
_ = 0 ∈ ns ∋ -42
