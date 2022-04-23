module Prelude.Ord where

open import Prelude.Init
open import Prelude.Lists
open import Prelude.Decidable
open import Prelude.Orders
open import Prelude.DecEq

record Ord (A : Set ℓ) : Set (lsuc ℓ) where
  field _≤_ _<_ : Rel₀ A
  _≰_ = ¬_ ∘₂ _≤_
  _≮_ = ¬_ ∘₂ _<_
  _≥_ = flip _≤_
  _>_ = flip _<_
  _≱_ = ¬_ ∘₂ _≥_
  _≯_ = ¬_ ∘₂ _>_

  infix 4 _≤_ _≰_ _≥_ _≱_ _<_ _>_ _≮_ _≯_

  module _ ⦃ pre : Preorder _≤_ ⦄ where
    open Preorder pre public

  module _ ⦃ _ : _≤_ ⁇² ⦄ where
    _≤?_ : Decidable² _≤_
    _≤?_ = dec²
    _≤ᵇ_ = isYes ∘₂ _≤?_
    _≰?_ = ¬? ∘₂ _≤?_
    _≰ᵇ_ = isYes ∘₂ _≰?_
    _≥?_ = flip _≤?_
    _≥ᵇ_ = isYes ∘₂ _≥?_
    _≱?_ = ¬? ∘₂ _≥?_
    _≱ᵇ_ = isYes ∘₂ _≱?_
    infix 4 _≤?_ _≤ᵇ_ _≰?_ _≰ᵇ_ _≥?_ _≥ᵇ_ _≱?_ _≱ᵇ_

    min max : Op₂ A
    min x y = if ⌊ x ≤? y ⌋ then x else y
    max x y = min y x

    minimum maximum : A → List A → A
    minimum = foldl min
    maximum = foldl max

    minimum⁺ maximum⁺ : List⁺ A → A
    minimum⁺ (x ∷ xs) = minimum x xs
    maximum⁺ (x ∷ xs) = maximum x xs

    module _ ⦃ _ : DecEq A ⦄ ⦃ _ : TotalOrder _≤_ ⦄ where
      open import Data.List.Sort.MergeSort
        (record { Carrier = A ; _≈_ = _ ; _≤_ = _ ; isDecTotalOrder = it })
        public
        using (sort)
      open import Data.List.Relation.Unary.Sorted.TotalOrder
        (record {isTotalOrder = it})
        as S public
        using (Sorted)

      instance
        DecSorted : Sorted ⁇¹
        DecSorted .dec = S.sorted? dec² _

      Sorted? : Decidable¹ Sorted
      Sorted? = dec¹

  module _ ⦃ _ : _<_ ⁇² ⦄ where
    _<?_ : Decidable² _<_
    _<?_ = dec²
    _≮?_ = ¬? ∘₂ _<?_
    _>?_ = flip _<?_
    _≯?_ = ¬? ∘₂ _>?_

    infix 4 _<?_ _>?_ _≮?_ _≯?_

  module _ ⦃ _ : DecEq A ⦄ ⦃ _ : StrictTotalOrder _<_ ⦄ where
    private STO = record { isStrictTotalOrder = it }

    module OrdTree where
      open import Data.Tree.AVL STO public
    module OrdMap where
      open import Data.Tree.AVL.Map STO public
    module OrdSet where
      open import Data.Tree.AVL.Sets STO public

open Ord ⦃...⦄ public

private variable X : Set ℓ

instance
  Ord-ℕ : Ord ℕ
  Ord-ℕ = record {Nat}

  DecOrd-ℕ : _≤_ ⁇²
  DecOrd-ℕ .dec = _ Nat.≤? _

  DecStrictOrd-ℕ : _<_ ⁇²
  DecStrictOrd-ℕ .dec = _ Nat.<? _

  Preorderℕ-≤ : Preorder _≤_
  Preorderℕ-≤ = record {Nat; ≤-refl = Nat.≤-reflexive refl}

  PartialOrderℕ-≤ : PartialOrder _≤_
  PartialOrderℕ-≤ = record {Nat}

  TotalOrderℕ-≤ : TotalOrder _≤_
  TotalOrderℕ-≤ = record {Nat}

  StrictPartialOrderℕ-< : StrictPartialOrder _<_
  StrictPartialOrderℕ-< = record {Nat}

  StrictTotalOrderℕ-< : StrictTotalOrder _<_
  StrictTotalOrderℕ-< = record {Nat}

  Ord-ℤ : Ord ℤ
  Ord-ℤ = record {Integer}

  DecOrd-ℤ : _≤_ ⁇²
  DecOrd-ℤ .dec = _ Integer.≤? _

  DecStrictOrd-ℤ : _<_ ⁇²
  DecStrictOrd-ℤ .dec = _ Integer.<? _

  Preorderℤ-≤ : Preorder _≤_
  Preorderℤ-≤ = record {Integer; ≤-refl = Integer.≤-reflexive refl}

  PartialOrderℤ-≤ : PartialOrder _≤_
  PartialOrderℤ-≤ = record {Integer}

  TotalOrderℤ-≤ : TotalOrder _≤_
  TotalOrderℤ-≤ = record {Integer}

  StrictPartialOrderℤ-< : StrictPartialOrder _<_
  StrictPartialOrderℤ-< = record {Integer; <-resp₂-≡ = subst (_ <_) , subst (_< _)}

  StrictTotalOrderℤ-< : StrictTotalOrder _<_
  StrictTotalOrderℤ-< = record {Integer}

  Ord-Maybe : ⦃ Ord X ⦄ → Ord (Maybe X)
  Ord-Maybe {X = X} = record {_≤_ = _≤ᵐ_; _<_ = _<ᵐ_}
    where
      _≤ᵐ_ _<ᵐ_ : Rel (Maybe X) _
      nothing ≤ᵐ _       = ⊤
      just _  ≤ᵐ nothing = ⊥
      just v  ≤ᵐ just v′ = v ≤ v′

      -- m <ᵐ m′ = (m ≤ᵐ m′) × (m ≢ m′)
      nothing <ᵐ nothing = ⊥
      nothing <ᵐ just _  = ⊤
      just _  <ᵐ nothing = ⊥
      just v  <ᵐ just v′ = v < v′

-- T0D0: cannot declare these as instances without breaking instance resolution.
module Maybe-DecOrd where
--   instance
  DecOrd-Maybe : ⦃ _ : Ord X ⦄ → ⦃ _ : _≤_ {A = X} ⁇² ⦄ → _≤_ {A = Maybe X} ⁇²
  DecOrd-Maybe              {x = nothing} {_}       .dec = yes tt
  DecOrd-Maybe              {x = just _}  {nothing} .dec = no λ ()
  DecOrd-Maybe ⦃ _ ⦄ ⦃ ≤? ⦄ {x = just _}  {just _}  .dec = dec ⦃ ≤? ⦄

  _≤?ᵐ_ : ⦃ _ : Ord X ⦄ → ⦃ _ : _≤_ {A = X} ⁇² ⦄ → Decidable² (_≤_ {A = Maybe X})
  x ≤?ᵐ y = DecOrd-Maybe {x = x} {y} .dec

  DecStrictOrd-Maybe : ⦃ _ : Ord X ⦄ → ⦃ _ : _<_ {A = X} ⁇² ⦄ → _<_ {A = Maybe X} ⁇²
  DecStrictOrd-Maybe              {x = nothing} {nothing} .dec = no λ ()
  DecStrictOrd-Maybe              {x = nothing} {just _}  .dec = yes tt
  DecStrictOrd-Maybe              {x = just _}  {nothing} .dec = no λ ()
  DecStrictOrd-Maybe ⦃ _ ⦄ ⦃ <? ⦄ {x = just _}  {just _}  .dec = dec ⦃ <? ⦄

  _<?ᵐ_ : ⦃ _ : Ord X ⦄ → ⦃ _ : _<_ {A = X} ⁇² ⦄ → Decidable² (_<_ {A = Maybe X})
  x <?ᵐ y = DecStrictOrd-Maybe {x = x} {y} .dec

postulate
  ∀≤max⁺ : ∀ (ts : List⁺ ℕ) → All⁺ (_≤ maximum⁺ ts) ts
  ∀≤max : ∀ t₀ (ts : List ℕ) → All (_≤ maximum t₀ ts) ts

private
  open import Prelude.Nary

  _ : sort (List ℤ ∋ []) ≡ []
  _ = refl

  _ : sort ⟦ 1 , 3 , 2 , 0 ⟧ ≡ ⟦ 0 , 1 , 2 , 3 ⟧
  _ = refl

  _ : True $ Sorted? ⟦ 1 , 6 , 15 ⟧
  _ = tt
