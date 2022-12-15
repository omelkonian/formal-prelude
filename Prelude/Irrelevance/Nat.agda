{-# OPTIONS --safe #-}
module Prelude.Irrelevance.Nat where

open import Prelude.Init
open Nat
open import Prelude.Irrelevance.Core

instance
  ·-≤ℕ : ·² _≤_
  ·-≤ℕ = λ where .∀≡ → ≤-irrelevant
