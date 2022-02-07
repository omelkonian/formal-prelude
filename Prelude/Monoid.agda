module Prelude.Monoid where

open import Prelude.Init
open import Prelude.Semigroup public

record Monoid (A : Set ℓ) : Set ℓ where
  field
    overlap ⦃ sm ⦄ : Semigroup A
    ε : A
open Monoid ⦃ ... ⦄ public hiding (sm)

record MonoidLaws (A : Set ℓ) (_~_ : Rel A ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
  field
    overlap ⦃ super ⦄ : Monoid A
    ε-identity : Alg.Identity _≡_ (super .ε) (super .Monoid.sm ._◇_)
open MonoidLaws ⦃...⦄ public hiding (super)

private variable A : Set

instance
  Monoid-List : Monoid (List A)
  Monoid-List .ε = []

  MonoidLaws-List : MonoidLaws (List A) _≡_
  MonoidLaws-List = record {ε-identity = L.++-identityˡ , L.++-identityʳ}

  Monoid-Vec : Monoid (∃ (Vec A))
  Monoid-Vec .ε = 0 , []

  Monoid-String : Monoid String
  Monoid-String .ε   = ""

Monoid-ℕ-+ = Monoid ℕ ∋ λ where .ε → 0
  where instance _ = Semigroup-ℕ-+
MonoidLaws-ℕ-+ = MonoidLaws ℕ _≡_ ∋ record {ε-identity = Nat.+-identityˡ , Nat.+-identityʳ}
  where instance _ = Monoid-ℕ-+

Monoid-ℕ-* = Monoid ℕ ∋ λ where .ε → 1
  where instance _ = Semigroup-ℕ-*
MonoidLaws-ℕ-* = MonoidLaws ℕ _≡_ ∋ record {ε-identity = Nat.*-identityˡ , Nat.*-identityʳ}
  where instance _ = Monoid-ℕ-*
