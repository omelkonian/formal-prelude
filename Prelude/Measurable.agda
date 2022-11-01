module Prelude.Measurable where

open import Function
open import Level renaming (suc to lsuc)
open import Induction
open import Induction.WellFounded
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Induction
open import Relation.Binary
import Relation.Binary.Construct.On as On

open import Prelude.General

record Measurable {ℓ} (A : Set ℓ) : Set ℓ where
  field
    ∣_∣ : A → ℕ

open Measurable ⦃...⦄ public

private
  variable
    a b : Level
    A : Set a
    B : Set b

instance
  Measurable-ℕ : Measurable ℕ
  Measurable-ℕ .∣_∣ x = x

  Measurable-⊎ : ⦃ _ : Measurable A ⦄ ⦃ _ : Measurable B ⦄ → Measurable (A ⊎ B)
  Measurable-⊎ .∣_∣ (inj₁ x) = ∣ x ∣
  Measurable-⊎ .∣_∣ (inj₂ x) = ∣ x ∣


∃Measurable : Set₁
∃Measurable = Σ[ A ∈ Set ] (Measurable A) × A

toMeasure : ∀ {A : Set} ⦃ _ : Measurable A ⦄ → A → ∃Measurable
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

_≺ᵐ_ : ∀ {A B : Set} ⦃ _ : Measurable A ⦄ ⦃ _ : Measurable B ⦄ → A → B → Set
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

private
  instance _ = Measurable-List₁

  list>0 : ∀ ⦃ _ : Measurable A ⦄ (xs : List A)
    → ∣ xs ∣ > 0
  list>0 [] = s≤s z≤n
  list>0 (x ∷ xs) with ∣ x ∣
  ... | 0     = list>0 xs
  ... | suc _ = s≤s z≤n

  ≺ᵐ-∷ : ∀ {A : Set} ⦃ _ : Measurable A ⦄ (x : A) (xs : List A)
    → (x ≺ᵐ (x ∷ xs))
  ≺ᵐ-∷ x xs = x<x+y ∣ x ∣ (list>0 xs)
