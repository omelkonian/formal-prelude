{-# OPTIONS --sized-types #-}
module Prelude.Streams where

open import Prelude.Init
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Ord

open import Size
open import Codata.Thunk as TH
open import Codata.Stream

SizedSet[_↝_] : ∀ ℓ ℓ′ → Set (lsuc ℓ ⊔ₗ lsuc ℓ′)
SizedSet[ ℓ ↝ ℓ′ ] = SizedSet ℓ → SizedSet ℓ′

SizedSet↑ : Setω
SizedSet↑ = ∀ {ℓ} → SizedSet[ ℓ ↝ ℓ ]

Stream∞ : Set↑
Stream∞ A = Stream A ∞

Thunk∞ : SizedSet ℓ → Set ℓ
Thunk∞  A = Thunk A ∞

Thunk∞^P : ∀ {F : SizedSet ℓ} → (F ∞ → Set ℓ) → Pred (Thunk∞ F) ℓ
Thunk∞^P P = Thunk^P (λ _ → P) ∞

private variable
  A B : Set
  i j : Size

-- mkThunk : ∀ {F : SizedSet ℓ} {i} → (∀ {j} → F j) → Thunk F i
-- pattern mkThunk x = record {force = x}

infix 4 _∈∞_ _∉ˢ_

data _∈∞_ : A → Stream∞ A → Set where
  here  : ∀ {x : A} {xs}                      → x ∈∞ x ∷ xs
  there : ∀ {x y : A} {xs} → x ∈∞ (xs .force) → x ∈∞ y ∷ xs

_∉ˢ_ : A → Stream∞ A → Set
_∉ˢ_ = ¬_ ∘₂ _∈∞_

_ : 0 ∈∞ nats
_ = here

_ : 1 ∈∞ nats
_ = there here

_ : 2 ∈∞ nats
_ = there $′ there here

data Unique∞ : Pred₀ (Stream∞ A) where
  isUniq : ∀ {x : A} {xs : Stream∞ A} →
    ∙ x ∉ˢ xs
    ∙ Unique∞ xs
      ─────────────────────────────────
      Unique∞ (x ∷ record {force = xs})

unfold′ : (A → A × A) → A → Stream A i
unfold′ next seed =
  let (seed′ , b) = next seed
  in b ∷ record {force = unfold′ next seed′}
  module ⟫unfold where


iterate′ : (A → A) → A → Stream∞ A
iterate′ f = unfold′ < f , id >

nats′ : Stream∞ ℕ
nats′ = iterate′ suc zero

-- data Unique∞ : Pred₀ (Stream∞ A) where
--   isUniq : ∀ {x : A} {xs : Thunk∞ (Stream A)} →
--     ∙ Thunk∞^P (x ∉ˢ_) xs
--     ∙ Thunk∞^P Unique∞ xs
--       ───────────────────
--       Unique∞ (x ∷ xs)

-- Unique-unfold : ∀ (next : ℕ → ℕ × ℕ) (seed : ℕ) →
--   (∀ x → x < next x .proj₁)
--   ─────────────────────────
--   Unique∞ (unfold next seed)
-- Unique-unfold next seed seed<
--   -- with (seed′ , x) ← next seed
--   -- with xs ← unfold next seed′
--     = isUniq {x = x} {xs = _} x∉ (record { force = Unique-unfold next seed′ seed< }) -- (λ where .force → IH′)
--     where
--       seed′ = next seed .proj₁
--       x     = next seed .proj₂

--       x∉ : Thunk∞^P (x ∉ˢ_) _
--       x∉ = record { force = λ x₁ → {!!} }

--       IH′ : Unique∞ (unfold next seed′)
--       IH′ = Unique-unfold next seed′ seed<
  -- isUniq {!!} {!Unique-unfold next seed′ ?!}
  -- isUniq ({!!})
  --        (Unique-unfold next (next seed .proj₁) seed<)
  -- isUniq (λ where .force → {!!})
  --        (λ where .force → Unique-unfold next (next seed .proj₁) seed<)

-- Unique-iterate : ∀ (f : ℕ → ℕ) (x : ℕ) →
--   (∀ x → x < f x)
--   ──────────────────────
--   Unique∞ (iterate′ f x)
-- Unique-iterate f = Unique-unfold < f , id >

-- Unique-nats : Unique∞ nats′
-- Unique-nats = Unique-iterate suc zero λ _ → Nat.≤-refl


-- -- Unique∞ : Pred₀ (Stream∞ A)
-- -- Unique∞ = ?

-- -- filterS : (A → Bool) → Stream∞ A → Stream∞ A
-- -- filterS f (x ∷ xs) =
-- --   if f x then
-- --     x ∷ (λ where .force → filterS f (xs .force))
-- --   else
-- --     {!!} -- xs′

-- -- ∁ : List ℕ → Stream∞ ℕ
-- -- ∁ xs = filterS (_∈ᵇ xs) nats

-- -- without : ℕ → Stream∞ ℕ → Stream∞ ℕ
-- -- without x (y ∷ ys) =
-- --   if x == y then
-- --     without x (ys .force)
-- --   else
-- --     y ∷ record { force = without x (ys .force) }

-- -- ∁ : List ℕ → Stream∞ ℕ
-- -- ∁ [] = nats
-- -- ∁ (x ∷ xs) = without x (∁ xs)
