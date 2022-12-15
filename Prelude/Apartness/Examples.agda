{-# OPTIONS --with-K #-}
module Prelude.Apartness.Examples where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Lists.Dec
open import Prelude.Decidable
open import Prelude.Apartness

private variable X : Type ℓ; n : ℕ

private
  _ : List X // List X
  _ = it

  _ : Vec X n // Vec X n
  _ = it

  _ : Vec X n // List X
  _ = it

  _ : List⁺ X // Vec X n
  _ = it

  _ : T (isYes ((List ℕ ∋ []) ♯? (List ℕ ∋ [])))
  _ = auto

  -- T0D0: improve `auto` to cover this
  _ : (List ℕ ∋ []) ♯ (List ℕ ∋ [])
  _ = toWitness {Q = ¿ (List ℕ ∋ []) ♯ (List ℕ ∋ []) ¿} auto
