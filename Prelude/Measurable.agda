{-# OPTIONS --safe #-}
module Prelude.Measurable where

open import Induction
open import Induction.WellFounded
open import Data.Nat.Induction
import Relation.Binary.Construct.On as On

open import Prelude.Init; open SetAsType
open Nat
open import Prelude.General
open import Prelude.DecEq.Core

record Measurable {ℓ} (A : Type ℓ) : Type ℓ where
  field
    ∣_∣ : A → ℕ

open Measurable ⦃...⦄ public

private
  variable
    a b : Level
    A : Type a
    B : Type b

instance
  Measurable-ℕ : Measurable ℕ
  Measurable-ℕ .∣_∣ x = x

  Measurable-⊎ : ⦃ _ : Measurable A ⦄ ⦃ _ : Measurable B ⦄ → Measurable (A ⊎ B)
  Measurable-⊎ .∣_∣ (inj₁ x) = ∣ x ∣
  Measurable-⊎ .∣_∣ (inj₂ x) = ∣ x ∣


∃Measurable : Type₁
∃Measurable = Σ[ A ∈ Type ] (Measurable A) × A

toMeasure : ∀ {A : Type} ⦃ _ : Measurable A ⦄ → A → ∃Measurable
toMeasure ⦃ mx ⦄ x = _ , mx , x

-- NB: this can be used when you want a *heterogeneous* well-founded relation
instance
  Measurable∃ : Measurable ∃Measurable
  Measurable∃ .∣_∣ (_ , record {∣_∣ = f} , x) = f x

module _ ⦃ _ : Measurable A ⦄ where

  _≺_ : Rel A 0ℓ
  _≺_ = _<_ on ∣_∣

  ≺-wf : WellFounded _≺_
  ≺-wf = On.wellFounded ∣_∣ <-wellFounded

  ≺-rec : Recursor (WfRec _≺_)
  ≺-rec = All.wfRec ≺-wf 0ℓ

_≺ᵐ_ : ∀ {A B : Type} ⦃ _ : Measurable A ⦄ ⦃ _ : Measurable B ⦄ → A → B → Type
x ≺ᵐ y = toMeasure x ≺ toMeasure y

-- alternatives for products
Measurable-×ˡ : ⦃ _ : Measurable A ⦄ → Measurable (A × B)
Measurable-×ˡ .∣_∣ (x , _) = ∣ x ∣

Measurable-×ʳ : ⦃ _ : Measurable B ⦄ → Measurable (A × B)
Measurable-×ʳ .∣_∣ (_ , x) = ∣ x ∣

-- alternatives for lists
Measurable-List₀ : Measurable (List A)
Measurable-List₀ .∣_∣ = length

Measurable-List₁ : ⦃ _ : Measurable A ⦄ → Measurable (List A)
Measurable-List₁ {A = A} .∣_∣ = go
  where
    go : List A → ℕ
    go [] = 1
    go (x ∷ xs) = ∣ x ∣ + go xs
