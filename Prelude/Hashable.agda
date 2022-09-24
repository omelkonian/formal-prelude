module Prelude.Hashable where

open import Prelude.Init

open import Prelude.Bitstring

record Hashable (A : Set ℓ) : Set ℓ where
  field _♯ : A → Bitstring
open Hashable ⦃...⦄ public

instance
  Hashable-ℕ : Hashable ℕ
  Hashable-ℕ ._♯ = fromℕ
