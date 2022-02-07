module Prelude.Semigroup where

open import Prelude.Init

record Semigroup (A : Set ℓ) : Set ℓ where
  infixr 5 _◇_ _<>_
  field _◇_ : A → A → A
  _<>_ = _◇_
open Semigroup ⦃...⦄ public

{-
record CommutativeSemigroup (A : Set ℓ) (_~_ : Rel A ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
  field
    overlap ⦃ sm ⦄ : Semigroup A
    ◇-comm : Alg.Commutative _~_ (sm ._◇_)
open CommutativeSemigroup ⦃...⦄ public hiding (sm)

record AssociativeSemigroup (A : Set ℓ) (_~_ : Rel A ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
  field
    overlap ⦃ sm ⦄ : Semigroup A
    ◇-assocʳ : Alg.Associative _~_ (sm ._◇_)
open AssociativeSemigroup ⦃...⦄ public hiding (sm)
-}

record SemigroupLaws (A : Set ℓ) (_≈_ : Rel A ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
  open Alg _≈_
  field
    overlap ⦃ sm ⦄ : Semigroup A
    ◇-comm   : Commutative _◇_
    ◇-assocʳ : Associative _◇_
open SemigroupLaws ⦃...⦄ public hiding (sm)

private variable A : Set ℓ

instance
  Semigroup-List : Semigroup (List A)
  Semigroup-List ._◇_ = _++_

  -- AssocSemigroup-List : AssociativeSemigroup (List A) _≡_
  -- AssocSemigroup-List = record {◇-assocʳ = L.++-assoc}

  Semigroup-List⁺ : Semigroup (List⁺ A)
  Semigroup-List⁺ ._◇_ = _⁺++⁺_

  Semigroup-∃Vec : Semigroup (∃ (Vec A))
  Semigroup-∃Vec ._◇_ (_ , v) (_ , v′) = _ , (v V.++ v′)

  Semigroup-String : Semigroup String
  Semigroup-String ._◇_ = Str._++_


Semigroup-ℕ-+ = Semigroup ℕ ∋ λ where ._◇_ → _+_
-- AssocSemigroup-ℕ-+ = AssociativeSemigroup ℕ _≡_ ∋ record {◇-assocʳ = Nat.+-assoc}
--   where instance _ = Semigroup-ℕ-+
-- CommSemigroup-ℕ-+ = CommutativeSemigroup ℕ _≡_ ∋ record {◇-comm = Nat.+-comm}
--   where instance _ = Semigroup-ℕ-+
SemigroupLaws-ℕ-+ = SemigroupLaws ℕ _≡_ ∋ record {◇-assocʳ = Nat.+-assoc; ◇-comm = Nat.+-comm}
  where instance _ = Semigroup-ℕ-+

Semigroup-ℕ-* = Semigroup ℕ ∋ λ where ._◇_ → _*_
-- AssocSemigroup-ℕ-* = AssociativeSemigroup ℕ _≡_ ∋ record {◇-assocʳ = Nat.*-assoc}
--   where instance _ = Semigroup-ℕ-*
-- CommSemigroup-ℕ-* = CommutativeSemigroup ℕ _≡_ ∋ record {◇-comm = Nat.*-comm}
--   where instance _ = Semigroup-ℕ-*
SemigroupLaws-ℕ-* = SemigroupLaws ℕ _≡_ ∋ record {◇-assocʳ = Nat.*-assoc; ◇-comm = Nat.*-comm}
  where instance _ = Semigroup-ℕ-*
