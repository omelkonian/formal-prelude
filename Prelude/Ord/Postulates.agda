module Prelude.Ord.Postulates where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Ord.Core
open import Prelude.Ord.Instances
open import Prelude.Ord.Irrelevant

instance
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
  postulate
    ·Ord-Char : ·Ord Char

  Ord⁺⁺-Char : Ord⁺⁺ Char
  Ord⁺⁺-Char = mkOrd⁺⁺

  postulate
    OrdLaws-String : OrdLaws String
    ·Ord-String : ·Ord String

  Ord⁺⁺-String : Ord⁺⁺ String
  Ord⁺⁺-String = mkOrd⁺⁺
