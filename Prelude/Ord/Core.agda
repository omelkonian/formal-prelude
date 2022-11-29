module Prelude.Ord.Core where

import Data.List.Relation.Binary.Lex.Strict as StrictLex
import Relation.Binary.Construct.On as On

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Lists
open Binary

record Ord (A : Type ℓ) ⦃ _ : DecEq A ⦄ : Typeω where
  field
    {relℓ} : Level
    _≤_ : Rel A relℓ
    _<_ : Rel A relℓ
    ⦃ Dec-≤ ⦄ : _≤_ ⁇²
    ⦃ Dec-< ⦄ : _<_ ⁇²

  _≰_ = ¬_ ∘₂ _≤_; _≥_ = flip _≤_; _≱_ = ¬_ ∘₂ _≥_
  _≤?_ = Decidable² _≤_ ∋ dec²; _≤ᵇ_ = isYes ∘₂ _≤?_
  _≰?_ = ¬? ∘₂ _≤?_; _≰ᵇ_ = isYes ∘₂ _≰?_
  _≥?_ = flip _≤?_; _≥ᵇ_ = isYes ∘₂ _≥?_
  _≱?_ = ¬? ∘₂ _≥?_; _≱ᵇ_ = isYes ∘₂ _≱?_
  _≮_ = ¬_ ∘₂ _<_; _>_ = flip _<_; _≯_ = ¬_ ∘₂ _>_
  _<?_ = Decidable² _<_ ∋ dec²; _<ᵇ_ = isYes ∘₂ _<?_
  _≮?_ = ¬? ∘₂ _<?_; _≮ᵇ_ = isYes ∘₂ _≮?_
  _>?_ = flip _<?_; _>ᵇ_ = isYes ∘₂ _>?_
  _≯?_ = ¬? ∘₂ _>?_; _≯ᵇ_ = isYes ∘₂ _≯?_
  infix 4 _≤_ _≰_ _≥_ _≱_ _≤?_ _≤ᵇ_ _≰?_ _≰ᵇ_ _≥?_ _≥ᵇ_ _≱?_ _≱ᵇ_
          _<_ _>_ _≮_ _≯_ _<?_ _<ᵇ_ _≮?_ _≮ᵇ_ _>?_ _>ᵇ_ _≯?_ _≯ᵇ_

  min max : Op₂ A
  min x y = if ⌊ x ≤? y ⌋ then x else y
  max x y = if ⌊ y ≤? x ⌋ then x else y

  minimum maximum : A → List A → A
  minimum = foldl min
  maximum = foldl max

  minimum⁺ maximum⁺ : List⁺ A → A
  minimum⁺ (x ∷ xs) = minimum x xs
  maximum⁺ (x ∷ xs) = maximum x xs

  module _ {x} {y} {ys : List A} where

    minimum-skip :
      x ≤ y
      ─────────────────────────────────
      minimum x (y ∷ ys) ≡ minimum x ys
    minimum-skip x≤ rewrite dec-yes (x ≤? y) x≤ .proj₂ = refl

    maximum-skip :
      y ≤ x
      ─────────────────────────────────
      maximum x (y ∷ ys) ≡ maximum x ys
    maximum-skip y≤ rewrite dec-yes (y ≤? x) y≤ .proj₂ = refl

  postulate
    ∀≤max⁺ : ∀ (xs : List⁺ A) → All⁺ (_≤ maximum⁺ xs) xs
    ∀≤max : ∀ x (xs : List A) → All (_≤ maximum x xs) xs

  ∀≤⇒≡max : ∀ {x} {xs : List A} →
    All (_≤ x) xs
    ────────────────
    x ≡ maximum x xs
  ∀≤⇒≡max [] = refl
  ∀≤⇒≡max {x = x} {xs = y ∷ xs} (py ∷ p) =
    begin x                  ≡⟨ ∀≤⇒≡max {xs = xs} p ⟩
          maximum x xs       ≡˘⟨ maximum-skip {ys = xs} py ⟩
          maximum x (y ∷ xs) ∎ where open ≡-Reasoning

open Ord ⦃...⦄ public

private variable A : Type ℓ; B : Type ℓ′

record OrdLaws (A : Type ℓ) ⦃ _ : DecEq A ⦄ ⦃ _ : Ord A ⦄ : Typeω where
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

  isPreorder = IsPreorder _≤_ ∋ record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive = λ where refl → ≤-refl
    ; trans = ≤-trans }

  isPartialOrder = IsPartialOrder _≤_ ∋ record
    { antisym = ≤-antisym
    ; isPreorder = isPreorder }

  isTotalOrder = IsTotalOrder _≤_ ∋ record
    { total = ≤-total
    ; isPartialOrder = isPartialOrder }

  open import Data.List.Relation.Unary.Sorted.TotalOrder
    (record {Carrier = A ; _≈_ = _ ; _≤_ =  _≤_ ; isTotalOrder = isTotalOrder})
    as S public
    using (Sorted)
  open import Data.List.Sort.MergeSort
    (record {Carrier = A ; _≈_ = _ ; _≤_ =  _≤_ ; isDecTotalOrder =
      record {_≟_ = _≟_ ; _≤?_ = _≤?_ ; isTotalOrder = isTotalOrder}})
    public
    using (sort; sort-↗; sort-↭)

  instance
    Dec-Sorted : Sorted ⁇¹
    Dec-Sorted .dec = S.sorted? _≤?_ _

  Sorted? = Decidable¹ Sorted ∋ dec¹

  postulate Unique-sort⁺ : ∀ {xs : List A} → Unique xs → Unique (sort xs)

  isStrictTotalOrder = IsStrictTotalOrder _<_ ∋ record
    { isEquivalence = PropEq.isEquivalence
    ; trans = <-trans
    ; compare = <-cmp
    }

  private STO = record { isStrictTotalOrder = isStrictTotalOrder }

  module OrdTree where
    open import Data.Tree.AVL STO public
  module OrdMap where
    open import Data.Tree.AVL.Map STO public
  module OrdSet where
    open import Data.Tree.AVL.Sets STO public

open OrdLaws ⦃...⦄ public

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
