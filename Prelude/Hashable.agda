{-# OPTIONS --with-K #-}
module Prelude.Hashable where

open import Prelude.Init; open SetAsType
open import Prelude.Bitstring
open import Prelude.FromN

record Hashable (A : Type ℓ) : Type ℓ where
  field _♯ : A → Bitstring
open Hashable ⦃...⦄ public

instance
  Hashable-ℕ : Hashable ℕ
  Hashable-ℕ ._♯ = fromℕ
