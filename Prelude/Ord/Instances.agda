{-# OPTIONS --safe #-}
module Prelude.Ord.Instances where

import Relation.Binary.Construct.On as On
import Data.List.Relation.Binary.Lex.Strict as StrictLex

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Decidable
open import Prelude.DecEq.Core

open import Prelude.Irrelevance.Nat

open import Prelude.Ord.Core
open import Prelude.Ord.Dec
open import Prelude.Ord.Irrelevant

instance
  Ord-ℕ : Ord ℕ
  Ord-ℕ = record {Nat}

  Dec-≤ℕ : Nat._≤_ ⁇²
  Dec-≤ℕ .dec = _ Nat.≤? _

  DecOrd-ℕ : DecOrd ℕ
  DecOrd-ℕ = record {}

  OrdLaws-ℕ : OrdLaws ℕ
  OrdLaws-ℕ = record {Nat; ≤∧≢⇒< = uncurry Nat.≤∧≢⇒<}

  ·Ord-ℕ : ·Ord ℕ
  ·Ord-ℕ = mk·Ord

  Ord⁺⁺-ℕ : Ord⁺⁺ ℕ
  Ord⁺⁺-ℕ = mkOrd⁺⁺

  Ord-ℤ = Ord ℤ ∋ record {Integer}

  Dec-≤ℤ : Integer._≤_ ⁇²
  Dec-≤ℤ .dec = _ Integer.≤? _

  Dec-<ℤ : Integer._<_ ⁇²
  Dec-<ℤ .dec = _ Integer.<? _

  DecOrd-ℤ : DecOrd ℤ
  DecOrd-ℤ = record {}

  OrdLaws-ℤ : OrdLaws ℤ
  OrdLaws-ℤ = record
    { Integer
    ; ≤∧≢⇒< = uncurry Integer.≤∧≢⇒<
    ; <-resp₂-≡ = subst (_ Integer.<_) , subst (Integer._< _)
    }

  Ord-Char = Ord Char ∋ record {Ch}

  Dec-≤Char : Ch._≤_ ⁇²
  Dec-≤Char .dec = _ Ch.≤? _

  DecOrd-Char : DecOrd Char
  DecOrd-Char = record {}

  Ord-String = Ord String ∋ record {Str}

  Dec-<String : Str._<_ ⁇²
  Dec-<String {x}{y} .dec = x Str.<? y

  Dec-≤String : Str._≤_ ⁇²
  Dec-≤String {x}{y} .dec = On.decidable _ _ (StrictLex.≤-decidable _≟_ Ch._<?_) x y

  DecOrd-String : DecOrd String
  DecOrd-String = λ where
    .Dec-≤ {x}{y} → Dec-≤String {x}{y}
    .Dec-< {x}{y} → Dec-<String {x}{y}
