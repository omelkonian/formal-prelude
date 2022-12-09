module Prelude.Ord.Instances where

import Relation.Binary.Construct.On as On
import Data.List.Relation.Binary.Lex.Strict as StrictLex

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Decidable
open import Prelude.DecEq

open import Prelude.Ord.Core
open import Prelude.Ord.Dec

instance
  Ord-ℕ = Ord ℕ ∋ record {Nat}

  Dec-≤ℕ : Nat._≤_ ⁇²
  Dec-≤ℕ .dec = _ Nat.≤? _

  DecOrd-ℕ : DecOrd ℕ
  DecOrd-ℕ = record {}

  OrdLaws-ℕ : OrdLaws ℕ
  OrdLaws-ℕ = record {Nat; ≤∧≢⇒< = uncurry Nat.≤∧≢⇒<}

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

  Ord-String = Ord String ∋ record {Str}

  Dec-<String : Str._<_ ⁇²
  Dec-<String {x}{y} .dec = x Str.<? y

  Dec-≤String : Str._≤_ ⁇²
  Dec-≤String {x}{y} .dec = On.decidable _ _ (StrictLex.≤-decidable _≟_ Ch._<?_) x y

  DecOrd-String : DecOrd String
  DecOrd-String = λ where
    .Dec-≤ {x}{y} → Dec-≤String {x}{y}
    .Dec-< {x}{y} → Dec-<String {x}{y}

  postulate OrdLaws-String : OrdLaws String
