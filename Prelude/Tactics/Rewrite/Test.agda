{-# OPTIONS --with-K #-}
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Tactics.Rewrite

module Prelude.Tactics.Rewrite.Test where

module M₁ (n m : ℕ) ⦃ _ : DecEq ℕ ⦄ where
  postulate
    n≡ : n ≡ m + 1
    P : Pred₀ ℕ
    p : P (m + 1)

  _ : P n
  _ = n≡ ≈: p

module M₂ (n m : ℕ) where
  open M₁ m n

  _ : P m
  _ = n≡ ⦃ it ⦄ ≈: p

module M₃ where
  open M₁ 0 1

  _ : P 0
  _ = n≡ ⦃ it ⦄ ≈: p

module M₄ where
  open M₁ 0

  _ : P 1 0
  _ = n≡ 1 ⦃ it ⦄ ≈: p 1

-- module M₅ where
--   open M₁

--   _ : P 0 1 0
--   _ = n≡ 0 1 ≈: p 0 1
