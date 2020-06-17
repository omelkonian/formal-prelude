{-# OPTIONS --postfix-projections #-}
module Prelude.Measurable where

open import Function
open import Level
open import Induction.WellFounded
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.Nat
open import Data.Nat.Induction
open import Relation.Binary

record Measurable {ℓ} (A : Set ℓ) : Set ℓ where
  field
    ∣_∣ : A → ℕ

open Measurable {{...}} public

private
  variable
    a b : Level
    A : Set a
    B : Set b

instance

  Measurable-⊎ : {{_ : Measurable A}} {{_ : Measurable B}} → Measurable (A ⊎ B)
  Measurable-⊎ .∣_∣ (inj₁ x) = ∣ x ∣
  Measurable-⊎ .∣_∣ (inj₂ x) = ∣ x ∣

  Measurable-List : {{_ : Measurable A}} → Measurable (List A)
  Measurable-List .∣_∣ []       = 1
  Measurable-List .∣_∣ (x ∷ xs) = ∣ x ∣ + ∣ xs ∣

  -- Measurable-× : {{_ : Measurable B}} → Measurable (A × B)
  -- Measurable-× .∣_∣ (_ , x) = ∣ x ∣

--

  Measurable-ℕ : Measurable ℕ
  Measurable-ℕ .∣_∣ x = x


module _ {{_ : Measurable A}} where

  _≺_ : Rel A 0ℓ
  _≺_ = _<_ on ∣_∣

  ≺-wf : WellFounded _≺_
  ≺-wf = InverseImage.wellFounded ∣_∣ <-wellFounded
