{-# OPTIONS --guardedness #-}
module Prelude.Musical where

open import Prelude.Init; open SetAsType
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Ord

open import Codata.Musical.Notation
open import Codata.Musical.Stream
  renaming (_∈_ to _∈∞_)

private variable A B : Type

infix 4 _∉∞_

-- _∉∞_ : A → Stream A → Type
-- _∉∞_ = ¬_ ∘₂ _∈∞_

data Any∞ (P : Pred₀ A) : Pred₀ (Stream A) where

  here : ∀ {x : A} {xs : ∞ (Stream A)} →
    ∙ P x
      ───────────────
      Any∞ P (x ∷ xs)

  there : ∀ {x : A} {xs : ∞ (Stream A)} →
    ∙ ∞ (Any∞ P (♭ xs))
      ─────────────────
      Any∞ P (x ∷ xs)

data All∞ (P : Pred₀ A) : Pred₀ (Stream A) where

  _∷_ : ∀ {x : A} {xs : ∞ (Stream A)} →
    ∙ P x
    ∙ ∞ (All∞ P (♭ xs))
      ─────────────────
      All∞ P (x ∷ xs)

map∞ : (A → B) → ∞ A → ∞ B
map∞ f x = ♯ (f (♭ x))

All∞-map : ∀ {P Q : Pred₀ A} {xs : Stream A} →
  ∙ P ⊆¹ Q
  ∙ All∞ P xs
    ─────────
    All∞ Q xs
All∞-map f (px ∷ pxs) = f px ∷ ♯ All∞-map f (♭ pxs)
-- All∞-map f (px ∷ pxs) = f px ∷ map∞ (All∞-map f) pxs

_∉∞_ : A → Stream A → Type
x ∉∞ xs = All∞ (_≢ x) xs

-- data _∉∞_ : A → Stream A → Type where
--   _∷_ : ∀ {x y : A} {ys : ∞ (Stream A)} →
--     ∙ x ≢ y
--     ∙ ∞ (x ∉∞ ♭ ys)
--       ─────────────
--       x ∉∞ (y ∷ ys)



-- iter : (A → A) → A → Stream A
-- iter f x = x ∷ ♯ iter f (f x)

{-# TERMINATING #-}
iter-x< : ∀ (f : ℕ → ℕ) (x : ℕ) →
  (∀ x → x < f x)
  ──────────────────────────
  All∞ (x <_) (iterate f (f x))
iter-x< f x x< =
  x< x ∷ let IH = iter-x< f (f x) x< in ♯ All∞-map (Nat.<-trans (x< x)) IH
  -- let fxs = iter-x< f (f x) x< in case fxs of λ where (fx ∷ fxs) → ♯ (Nat.<-trans (x< x) fx ∷ {!!})
  -- map∞ (All∞-map (Nat.<-trans (x< x))) (♯ iter-x< f (f x) x<)
  -- ♯ All∞-map (Nat.<-trans (x< x)) (iter-x< f (f x) x<) -- (♭ ()

iter-x∉ : ∀ (f : ℕ → ℕ) (x : ℕ) →
  (∀ x → x < f x)
  ────────────────────
  x ∉∞ iterate f (f x)
iter-x∉ f x x< = All∞-map (≢-sym ∘ Nat.<⇒≢) $ iter-x< f x x<

nats : Stream ℕ
nats = iterate suc zero

_ : 0 ∈∞ nats
_ = here

_ : 1 ∈∞ nats
_ = there here

_ : 2 ∈∞ nats
_ = there $′ there here

data Unique∞ : Pred₀ (Stream A) where
  isUniq : ∀ {x : A} {xs : ∞ (Stream A)} →
    ∙ ∞ (x ∉∞ (♭ xs))
    ∙ ∞ (Unique∞ (♭ xs))
      ──────────────────
      Unique∞ (x ∷ xs)

Unique∞-iterate : ∀ (f : ℕ → ℕ) (x : ℕ) →
  (∀ x → x < f x)
  ─────────────────────
  Unique∞ (iterate f x)
Unique∞-iterate f x x< = isUniq (♯ iter-x∉ f x x<) (♯ (Unique∞-iterate f (f x) x<))

Unique∞-nats : Unique∞ nats
Unique∞-nats = Unique∞-iterate suc zero λ _ → Nat.≤-refl

-- filter∞ : (A → Bool) → (xs : Stream A) → Unique∞ xs → Stream A
-- filter∞ f (x ∷ xs) (isUniq x∉ uniq-xs) =
--   if f x then
--     x ∷ ♯ filter∞ f (♭ xs) (♭ uniq-xs)
--   else
--     filter∞ f (♭ xs) (♭ uniq-xs)

-- ∁ : List ℕ → Stream ℕ
-- ∁ xs = filter∞ (_∉ᵇ xs) nats Unique∞-nats

-- remove : (xs : Stream ℕ) → Unique∞ xs → ℕ → Stream ℕ
-- remove (x ∷ xs) (isUniq x∉ uniq-xs) y =
--   if x == y then
--     remove (♭ xs) (♭ uniq-xs) y
--   else
--     x ∷ ♯ remove (♭ xs) (♭ uniq-xs) y

_─_ : Σ (Stream ℕ) Unique∞ → List ℕ → Stream ℕ
(xs , uniq-xs) ─ [] = xs
(xs , uniq-xs) ─ (x ∷ ys) = {!(xs , uniq-xs) ─ ys!}

∁ : List ℕ → Stream ℕ
∁ xs = (-, Unique∞-nats) ─ xs
