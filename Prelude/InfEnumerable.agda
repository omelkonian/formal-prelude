------------------------------------------------------------
-- (Infinite) enumerable types that are in bijection with ℕ.
------------------------------------------------------------

-- {-# OPTIONS --safe #-}
module Prelude.InfEnumerable where

open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.Nats
open import Prelude.Membership using (_∈?_)
open import Prelude.Nary
open import Prelude.Lists.Combinatorics
open import Prelude.Lists.Sums
open import Prelude.Lists.Postulates
open import Prelude.Decidable
open import Prelude.DecEq.Core
open import Prelude.ToN
open import Prelude.FromN
open import Prelude.Ord.Core
open import Prelude.Ord.Instances

-- Enumerable∞ A = A ↔ ℕ
record Enumerable∞ (A : Type ℓ) : Type ℓ where
  field enum : A Fun.↔ ℕ
open Enumerable∞ ⦃...⦄ public

private variable A : Type ℓ

instance
  Enumerable∞-ℕ : Enumerable∞ ℕ
  Enumerable∞-ℕ .enum = record
    { f = id ; f⁻¹ = id
    ; cong₁ = λ{ refl → refl } ; cong₂ = λ{ refl → refl }
    ; inverse = (λ _ → refl) , (λ _ → refl) }

  Enumerable∞⇒ToN : ⦃ Enumerable∞ A ⦄ → Toℕ A
  Enumerable∞⇒ToN .toℕ = enum .Fun.Inverse.f

  Enumerable∞⇒FromN : ⦃ Enumerable∞ A ⦄ → Fromℕ A
  Enumerable∞⇒FromN .fromℕ = enum .Fun.Inverse.f⁻¹

freshℕ : (xs : List ℕ) → ∃ (_∉ xs)
freshℕ xs = suc (∑ℕ xs) , λ x∈ → ¬suc≰ _ (x∈∑ℕ x∈)
  where
    ¬suc≰ : ∀ n → suc n ≰ n
    ¬suc≰ (suc n) (s≤s p) = ¬suc≰ n p

minFreshℕ : (xs : List ℕ) → ∃ (_∉ xs)
minFreshℕ xs = go 0 (suc (∑ℕ xs))
  where
    go : ℕ → ℕ → ∃ (_∉ xs)
    go _ 0 = freshℕ xs
    go x (suc fuel) with x ∈? xs
    ... | no x∉ = x , x∉
    ... | yes _ = go (suc x) fuel

fromℕ∈⇒∈toℕ : ∀ ⦃ _ : Enumerable∞ A ⦄ n (xs : List A) → fromℕ n ∈ xs → n ∈ map toℕ xs
fromℕ∈⇒∈toℕ n xs x∈ =
  subst (_∈ map toℕ xs) (enum .Fun.Inverse.inverse .proj₁ n) $
  L.Mem.∈-map⁺ toℕ {x = fromℕ n} {xs = xs} x∈

fresh : ⦃ Enumerable∞ A ⦄ → (xs : List A) → ∃ (_∉ xs)
fresh xs =
  let n , n∉ = freshℕ (map toℕ xs)
  in  fromℕ n , n∉ ∘ fromℕ∈⇒∈toℕ _ _

minFresh : ⦃ Enumerable∞ A ⦄ → (xs : List A) → ∃ (_∉ xs)
minFresh xs =
  let n , n∉ = minFreshℕ (map toℕ xs)
  in  fromℕ n , n∉ ∘ fromℕ∈⇒∈toℕ _ _

fresh^_ : ⦃ Enumerable∞ A ⦄ → (n : ℕ) → (xs : List A) →
  Σ (Vec A n) (V.All.All (_∉ xs))
(fresh^ zero) xs = [] , V.All.[]
(fresh^ suc n) xs =
  let x , px = fresh xs
      xs , pxs = (fresh^ n) xs
  in x ∷ xs , px V.All.∷ pxs
