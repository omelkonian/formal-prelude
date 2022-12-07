module Prelude.Separated where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Setoid
open import Prelude.Setoid.Maybe
open import Prelude.PartialSemigroup
open import Prelude.PartialMonoid

-- ** A separation algebra is cancellative, partial commutative monoid (Σ, •, ε).
record Separated (Σ : Type ℓ) ⦃ _ : LawfulSetoid Σ ⦄ : Type (ℓ ⊔ₗ relℓ {A = Σ}) where
  field
    ⦃ ps ⦄ : PartialSemigroup Σ
    ⦃ ps-laws ⦄ : PartialSemigroupLaws Σ
    ⦃ pm ⦄ : PartialMonoid Σ
    ⦃ pm-laws ⦄ : PartialMonoidLaws Σ
    cancellative : ∀ (x : Σ) → Injective _≈_ _≈_ (x ◆_)

  -- ** induced relations

  -- "separateness"
  _#_ : Rel Σ _
  x # y = Is-just (x ◆ y )

  -- "substate"
  _≼_ : Rel Σ _
  x ≼ z = ∃ λ y → (x ◆ y) ≈ just z

  -- ** predicates over Σ
  ℙ : Type _
  ℙ = Pred Σ _

  emp : ℙ
  emp = _≈ ε

  open Unary

  _∗_ : ℙ → ℙ → Pred Σ _
  (p ∗ q) σ = ∃ λ (σ₀ : Σ) → ∃ λ (σ₁ : Σ)
    → (σ₀ # σ₁)
    × (σ₀ ∈ p)
    × (σ₁ ∈ q)

  -- ** precise predicates
  Prec : Pred ℙ _
  Prec p = ∀ σ → Irrelevant¹ (λ σₚ → (σₚ ∈ p) × (σₚ ≼ σ))

  Singleton : Pred ℙ _
  Singleton p = (_∈ p) ⊣⊢ (λ σ → ∃ (σ ≈_))

  private variable p : ℙ

  postulate Singleton⇒Prec : Singleton ⊆¹ Prec
  -- Singleton⇒Prec {p} single σ (px , ≼σ) (px′ , ≼σ′)
  --   with single .proj₁ px | single .proj₁ px′
  -- ... | s , refl | .s , refl
  --   = {!!}

open Separated ⦃...⦄ public


-- ⦃ _ : A // A ⦄
-- open import Prelude.Semigroup
-- open import Prelude.FinPartialFun
-- private

--   -- 1. heaps, as finite partial functions from l-values to r-values
--   module Heap (L RV : Type)
--     ⦃ _ : Semigroup L ⦄
--     -- ⦃ _ : Monoid L ⦄
--     ⦃ _ : Finable L ⦄
--     where

--     H = L ⇀ᶠⁱⁿ RV
--     instance
--       Sep-Heap : Separated≡ H
--       Sep-Heap = λ where
--         .ε → {!ε!} , {!!}
--         ._◆_ → {!!}
--         .unity → {!!}
--         .commutativity → {!!}
--         .associativity → {!!}
--         .cancellative → {!!}
--
--
