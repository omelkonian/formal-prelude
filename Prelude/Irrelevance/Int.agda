{-# OPTIONS --safe #-}
module Prelude.Irrelevance.Int where

open import Prelude.Init
open Integer
open import Prelude.Irrelevance.Core

instance
  ·-≤ℤ : ·² _≤_
  ·-≤ℤ = λ where .∀≡ → ≤-irrelevant

  ·-<ℤ : ·² _<_
  ·-<ℤ = λ where .∀≡ → <-irrelevant
