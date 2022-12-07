module Prelude.Ord.Instances where

import Relation.Binary.Construct.On as On
import Data.List.Relation.Binary.Lex.Strict as StrictLex

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Decidable
open import Prelude.DecEq

open import Prelude.Ord.Core

instance
  Dec-≤ℕ : Nat._≤_ ⁇²
  Dec-≤ℕ .dec = _ Nat.≤? _

  Ord-ℕ : Ord ℕ
  Ord-ℕ = record {Nat}

  OrdLaws-ℕ : OrdLaws ℕ
  OrdLaws-ℕ = record {Nat; ≤∧≢⇒< = uncurry Nat.≤∧≢⇒<}

  Dec-≤ℤ : Integer._≤_ ⁇²
  Dec-≤ℤ .dec = _ Integer.≤? _

  Dec-<ℤ : Integer._<_ ⁇²
  Dec-<ℤ .dec = _ Integer.<? _

  Ord-ℤ : Ord ℤ
  Ord-ℤ = record {Integer}

  OrdLaws-ℤ : OrdLaws ℤ
  OrdLaws-ℤ = record
    { Integer
    ; ≤∧≢⇒< = uncurry Integer.≤∧≢⇒<
    ; <-resp₂-≡ = subst (_ Integer.<_) , subst (Integer._< _)
    }

  Dec-≤Char : Ch._≤_ ⁇²
  Dec-≤Char .dec = _ Ch.≤? _

  Ord-Char : Ord Char
  Ord-Char = record {Ch}

  OrdLaws-Char : OrdLaws Char
  OrdLaws-Char = record
    { Ch
    ; ≤-refl = Ch.≤-reflexive refl
    ; <-trans = λ {i}{j}{k} → Ch.<-trans {i}{j}{k}
    ; ≤-total = ≤-total-Char
    ; <-resp₂-≡ = <-resp₂-≡-Char
    ; <⇒≤ = <⇒≤-Char
    ; <⇒≢ = <⇒≢-Char
    ; ≤∧≢⇒< = ≤∧≢⇒<-Char
    } where
      postulate
        ≤-total-Char : Total Ch._≤_
        <-resp₂-≡-Char : Ch._<_ Respects₂ _≡_
        <⇔≤∧≢-Char : _<_ ⇔² (Ch._≤_ ∩² _≢_)
        <⇒≤-Char : Ch._<_ ⇒² Ch._≤_
        <⇒≢-Char : Ch._<_ ⇒² _≢_
        ≤∧≢⇒<-Char : Ch._≤_ ∩² _≢_ ⇒² Ch._<_

  Dec-<String : Str._<_ ⁇²
  Dec-<String {x}{y} .dec = x Str.<? y

  Dec-≤String : Str._≤_ ⁇²
  Dec-≤String {x}{y} .dec = On.decidable _ _ (StrictLex.≤-decidable _≟_ Ch._<?_) x y

  Ord-String : Ord String
  Ord-String = record
    { Str
    ; Dec-≤ = λ {x}{y} → Dec-≤String {x}{y}
    ; Dec-< = λ {x}{y} → Dec-<String {x}{y}
    }

  postulate OrdLaws-String : OrdLaws String
