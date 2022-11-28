module Prelude.Ord.Core where

open import Prelude.Init; open SetAsType
open import Prelude.Lists
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Lift
open import Prelude.Orders

record Ord (A : Type ℓ) : Typeω where
  field
    {relℓ} : Level
    _≤_ _<_ : Rel A relℓ
  _≰_ = ¬_ ∘₂ _≤_
  _≮_ = ¬_ ∘₂ _<_
  _≥_ = flip _≤_
  _>_ = flip _<_
  _≱_ = ¬_ ∘₂ _≥_
  _≯_ = ¬_ ∘₂ _>_

  infix 4 _≤_ _≰_ _≥_ _≱_ _<_ _>_ _≮_ _≯_

  module _ ⦃ _ : _≤_ ⁇² ⦄ where
    _≤?_ : Decidable² _≤_
    _≤?_ = dec²; _≤ᵇ_ = isYes ∘₂ _≤?_
    _≰?_ = ¬? ∘₂ _≤?_; _≰ᵇ_ = isYes ∘₂ _≰?_
    _≥?_ = flip _≤?_; _≥ᵇ_ = isYes ∘₂ _≥?_
    _≱?_ = ¬? ∘₂ _≥?_; _≱ᵇ_ = isYes ∘₂ _≱?_
    infix 4 _≤?_ _≤ᵇ_ _≰?_ _≰ᵇ_ _≥?_ _≥ᵇ_ _≱?_ _≱ᵇ_

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

    module _ ⦃ _ : DecEq A ⦄ ⦃ _ : TotalOrder _≤_ ⦄ where
      open import Data.List.Sort.MergeSort
        (record { Carrier = A ; _≈_ = _ ; _≤_ = _ ; isDecTotalOrder = it })
        public
        using (sort; sort-↗; sort-↭)
      open import Data.List.Relation.Unary.Sorted.TotalOrder
        (record {isTotalOrder = it})
        as S public
        using (Sorted)

      instance
        DecSorted : Sorted ⁇¹
        DecSorted .dec = S.sorted? dec² _

      Sorted? : Decidable¹ Sorted
      Sorted? = dec¹

      postulate
        Unique-sort⁺ : ∀ {xs : List A} → Unique xs → Unique (sort xs)

  module _ ⦃ _ : _<_ ⁇² ⦄ where
    _<?_ : Decidable² _<_
    _<?_ = dec²; _<ᵇ_ = isYes ∘₂ _<?_
    _≮?_ = ¬? ∘₂ _<?_; _≮ᵇ_ = isYes ∘₂ _≮?_
    _>?_ = flip _<?_; _>ᵇ_ = isYes ∘₂ _>?_
    _≯?_ = ¬? ∘₂ _>?_; _≯ᵇ_ = isYes ∘₂ _≯?_
    infix 4 _<?_ _<ᵇ_ _≮?_ _≮ᵇ_ _>?_ _>ᵇ_ _≯?_ _≯ᵇ_

  module _ ⦃ _ : DecEq A ⦄ ⦃ _ : StrictTotalOrder _<_ ⦄ where
    private STO = record { isStrictTotalOrder = it }

    module OrdTree where
      open import Data.Tree.AVL STO public
    module OrdMap where
      open import Data.Tree.AVL.Map STO public
    module OrdSet where
      open import Data.Tree.AVL.Sets STO public

open Ord ⦃...⦄ public
