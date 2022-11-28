module Prelude.Irrelevance.Nat where

open import Prelude.Init
open import Prelude.Irrelevance.Core

instance
  ·-≤ℕ : ·² Nat._≤_
  ·-≤ℕ = λ where .∀≡ → Nat.≤-irrelevant
