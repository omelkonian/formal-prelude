module Prelude.Monoid where

open import Prelude.Init
open import Prelude.Semigroup public

record Monoid (A : Set ℓ) : Set ℓ where
  field
    overlap ⦃ sm ⦄ : Semigroup A
    ε : A
open Monoid ⦃ ... ⦄ public hiding (sm)

record MonoidLaws (A : Set ℓ) ⦃ _ : Monoid A ⦄ (_~_ : Rel A ℓ′) : Set (ℓ ⊔ₗ ℓ′) where
  open Alg _~_
  field ε-identity : Identity ε _◇_

  ε-identityˡ : LeftIdentity ε _◇_
  ε-identityˡ = ε-identity .proj₁

  ε-identityʳ : RightIdentity ε _◇_
  ε-identityʳ = ε-identity .proj₂
open MonoidLaws ⦃...⦄ public

MonoidLaws≡ : (A : Set ℓ) ⦃ _ : Monoid A ⦄ → Set ℓ
MonoidLaws≡ A = MonoidLaws A _≡_

private variable A : Set

instance
  Monoid-List : Monoid (List A)
  Monoid-List .ε = []

  MonoidLaws-List : MonoidLaws≡ (List A)
  MonoidLaws-List = record {ε-identity = L.++-identityˡ , L.++-identityʳ}

  Monoid-Vec : Monoid (∃ (Vec A))
  Monoid-Vec .ε = 0 , []

  Monoid-String : Monoid String
  Monoid-String .ε = ""

  Monoid-Maybe : ⦃ Monoid A ⦄ → Monoid (Maybe A)
  Monoid-Maybe .ε = nothing

  MonoidLaws-Maybe : ⦃ m : Monoid A ⦄ → ⦃ MonoidLaws≡ A ⦄ → MonoidLaws≡ (Maybe A)
  MonoidLaws-Maybe {A = A} = record {ε-identity = p , q}
    where open Alg≡
          p = LeftIdentity ε  _◇_ ∋ λ _ → refl
          q = RightIdentity ε _◇_ ∋ λ where (just _) → refl; nothing → refl

Monoid-ℕ-+ = Monoid ℕ ∋ λ where .ε → 0
  where instance _ = Semigroup-ℕ-+
MonoidLaws-ℕ-+ = MonoidLaws≡ ℕ ∋ record {ε-identity = Nat.+-identityˡ , Nat.+-identityʳ}
  where instance _ = Monoid-ℕ-+

Monoid-ℕ-* = Monoid ℕ ∋ λ where .ε → 1
  where instance _ = Semigroup-ℕ-*
MonoidLaws-ℕ-* = MonoidLaws≡ ℕ ∋ record {ε-identity = Nat.*-identityˡ , Nat.*-identityʳ}
  where instance _ = Monoid-ℕ-*
