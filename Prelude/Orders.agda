module Prelude.Orders where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable
open import Prelude.DecEq

module _ {A : Set ℓ} where

  module _ (_≤_ : Rel A ℓ′) where

    record Preorder : Set (ℓ ⊔ₗ ℓ′) where
      field
        ≤-refl  : Reflexive _≤_
        ≤-trans : Transitive _≤_
    open Preorder ⦃ ... ⦄ public

    record TotalPreorder : Set (ℓ ⊔ₗ ℓ′) where
      field
        ⦃ super ⦄ : Preorder
        ≤-pre-total : Total _≤_
    open TotalPreorder ⦃ ... ⦄ public

    record PartialOrder : Set (ℓ ⊔ₗ ℓ′) where
      field
        ⦃ super ⦄ : Preorder
        ≤-antisym : Antisymmetric _≡_ _≤_
    open PartialOrder ⦃ ... ⦄ public

    record TotalOrder : Set (ℓ ⊔ₗ ℓ′) where
      field
        ⦃ super ⦄ : PartialOrder
        ≤-total : Total _≤_
    open TotalOrder ⦃ ... ⦄ public

  module _ {_≤_ : Rel A ℓ′} where
    instance
      Preorder⇒IsPreorder : ⦃ Preorder _≤_ ⦄ → Binary.IsPreorder _≤_
      Preorder⇒IsPreorder = record
        { isEquivalence = PropEq.isEquivalence
        ; reflexive = λ{ refl → ≤-refl }; trans = ≤-trans }

      ⇒IsPartialOrder : ⦃ PartialOrder _≤_ ⦄ → Binary.IsPartialOrder _≤_
      ⇒IsPartialOrder = record { isPreorder = it; antisym = ≤-antisym }

      ⇒IsDecPartialOrder : ⦃ PartialOrder _≤_ ⦄ → ⦃ DecEq A ⦄ → ⦃ _≤_ ⁇² ⦄
        → Binary.IsDecPartialOrder _≤_
      ⇒IsDecPartialOrder = record { isPartialOrder = it ; _≟_ = _≟_ ; _≤?_ = dec² }

      ⇒IsTotalOrder : ⦃ TotalOrder _≤_ ⦄ → Binary.IsTotalOrder _≤_
      ⇒IsTotalOrder = record { isPartialOrder = it; total = ≤-total }

      ⇒IsDecTotalOrder : ⦃ TotalOrder _≤_ ⦄ → ⦃ DecEq A ⦄ → ⦃ _≤_ ⁇² ⦄
        → Binary.IsDecTotalOrder _≤_
      ⇒IsDecTotalOrder = record { isTotalOrder = it ; _≟_ = _≟_ ; _≤?_ = dec² }

  module _ (_<_ : Rel A ℓ′) where

    record StrictPartialOrder : Set (ℓ ⊔ₗ ℓ′) where
      field
        <-irrefl  : Irreflexive _≡_ _<_
        <-trans   : Transitive _<_
        <-resp₂-≡ : _<_ Respects₂ _≡_
    open StrictPartialOrder ⦃ ... ⦄ public

    record StrictTotalOrder : Set (ℓ ⊔ₗ ℓ′) where
      field
        ⦃ super ⦄ : StrictPartialOrder
        <-cmp     : Binary.Trichotomous _≡_ _<_
    open StrictTotalOrder ⦃ ... ⦄ public

  module _ {_<_ : Rel A ℓ′} where
    instance
      ⇒IsStrictPartialOrder : ⦃ StrictPartialOrder _<_ ⦄ → Binary.IsStrictPartialOrder _<_
      ⇒IsStrictPartialOrder = record
        { isEquivalence = PropEq.isEquivalence
        ; irrefl = <-irrefl; trans = <-trans; <-resp-≈ = <-resp₂-≡ }

      ⇒IsDecStrictPartialOrder : ⦃ StrictPartialOrder _<_ ⦄ → ⦃ DecEq A ⦄ → ⦃ _<_ ⁇² ⦄
        → Binary.IsDecStrictPartialOrder _<_
      ⇒IsDecStrictPartialOrder = record
        { isStrictPartialOrder = it ; _≟_ = _≟_ ; _<?_ = dec² }

      ⇒IsStrictTotalOrder : ⦃ StrictTotalOrder _<_ ⦄ → Binary.IsStrictTotalOrder _<_
      ⇒IsStrictTotalOrder = record
        { isEquivalence = PropEq.isEquivalence
        ; trans = <-trans; compare = <-cmp }
