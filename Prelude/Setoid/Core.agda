{-# OPTIONS --safe #-}
module Prelude.Setoid.Core where

open import Prelude.Init; open SetAsType

record ISetoid (A : Type ℓ) : Typeω where
  infix 4 _≈_ _≉_
  field
    {relℓ} : Level
    _≈_ : Rel A relℓ

  _≉_ : Rel A relℓ
  x ≉ y = ¬ (x ≈ y)

  module Alg≈ = Alg _≈_
open ISetoid ⦃...⦄ public

record SetoidLaws (A : Type ℓ) ⦃ _ : ISetoid A ⦄ : Typeω where
  field isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public
    renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans; reflexive to ≈-reflexive)

  mkSetoid : Setoid ℓ relℓ
  mkSetoid = record {Carrier = A; _≈_ = _≈_; isEquivalence = isEquivalence}

  import Relation.Binary.Reasoning.Setoid as BinSetoid
  module ≈-Reasoning = BinSetoid mkSetoid
open SetoidLaws ⦃...⦄ public

record LawfulSetoid (A : Type ℓ) : Typeω where
  field ⦃ is ⦄ : ISetoid A
        ⦃ obeys ⦄ : SetoidLaws A
instance
  mkLawful-Setoid : {A : Type ℓ} ⦃ _ : ISetoid A ⦄ → ⦃ SetoidLaws A ⦄ → LawfulSetoid A
  mkLawful-Setoid = record {}
open LawfulSetoid ⦃...⦄ using () public

_⟶_ : (A : Type ℓ) (B : Type ℓ′) ⦃ _ : LawfulSetoid A ⦄ ⦃ _ : LawfulSetoid B ⦄ → Set _
A ⟶ B = mkSetoid {A = A} Fun.Eq.⟶ mkSetoid {A = B}

private variable A : Type ℓ

mkISetoid≡ : ISetoid A
mkISetoid≡ = λ where
  .relℓ → _
  ._≈_ → _≡_

mkSetoidLaws≡ : SetoidLaws A ⦃ mkISetoid≡ ⦄
mkSetoidLaws≡ .isEquivalence = PropEq.isEquivalence

mkLawfulSetoid≡ : LawfulSetoid A
mkLawfulSetoid≡ = itω
  where instance _ = mkISetoid≡; _ = mkSetoidLaws≡
