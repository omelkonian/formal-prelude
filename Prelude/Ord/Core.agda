{-# OPTIONS --safe #-}
module Prelude.Ord.Core where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Decidable

record Ord (A : Type ℓ) : Type (lsuc ℓ) where
  field _≤_ _<_ : Rel A ℓ

  infix 4 _≤_ _≰_ _≥_ _≱_ _<_ _>_ _≮_ _≯_
  _≰_ = ¬_ ∘₂ _≤_; _≥_ = flip _≤_; _≱_ = ¬_ ∘₂ _≥_
  _≮_ = ¬_ ∘₂ _<_; _>_ = flip _<_; _≯_ = ¬_ ∘₂ _>_

open Ord ⦃...⦄ public

≤-from-< : ∀ {A : Set ℓ} → Rel A ℓ → Rel A ℓ
≤-from-< _<_ = λ x y → (x ≡ y) ⊎ (x < y)

mkOrd< : ∀ {A : Set ℓ} → Rel A ℓ → Ord A
mkOrd< _<_ = record {_<_ = _<_; _≤_ = ≤-from-< _<_}

record OrdLaws (A : Type ℓ) ⦃ _ : Ord A ⦄ : Type ℓ where
  field
    -- ≤ is a preorder
    ≤-refl  : Reflexive _≤_
    ≤-trans : Transitive _≤_
    -- ≤ is a partial order
    ≤-antisym : Antisymmetric _≡_ _≤_
    -- ≤ is a total order
    ≤-total : Total _≤_
    -- < is a strict partial order
    <-irrefl  : Irreflexive _≡_ _<_
    <-trans   : Transitive _<_
    <-resp₂-≡ : _<_ Respects₂ _≡_
    -- < is a strict total order
    <-cmp     : Binary.Trichotomous _≡_ _<_
    -- ≤ is the non-strict version of <
    <⇒≤ : _<_ ⇒² _≤_
    <⇒≢ : _<_ ⇒² _≢_
    ≤∧≢⇒< : _≤_ ∩² _≢_ ⇒² _<_

  <⇔≤∧≢ : _<_ ⇔² (_≤_ ∩² _≢_)
  <⇔≤∧≢ = (λ p → <⇒≤ p , <⇒≢ p) , ≤∧≢⇒<

  open Binary

  isPreorder = IsPreorder _≤_ ∋ record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive = λ where refl → ≤-refl
    ; trans = ≤-trans }

  isPartialOrder = IsPartialOrder _≤_ ∋ record
    { antisym = ≤-antisym
    ; isPreorder = isPreorder }

  isStrictPartialOrder = IsStrictPartialOrder _<_ ∋ record
    { isEquivalence = PropEq.isEquivalence
    ; irrefl = <-irrefl
    ; trans = <-trans
    ; <-resp-≈ = <-resp₂-≡ }

  isTotalOrder = IsTotalOrder _≤_ ∋ record
    { total = ≤-total
    ; isPartialOrder = isPartialOrder }

  isStrictTotalOrder = IsStrictTotalOrder _<_ ∋ record
    { isEquivalence = PropEq.isEquivalence
    ; trans = <-trans
    ; compare = <-cmp }

  private STO = record { isStrictTotalOrder = isStrictTotalOrder }

  module OrdTree where
    open import Data.Tree.AVL STO public
  module OrdMap where
    open import Data.Tree.AVL.Map STO public
  module OrdSet where
    open import Data.Tree.AVL.Sets STO public

open OrdLaws ⦃...⦄ public
