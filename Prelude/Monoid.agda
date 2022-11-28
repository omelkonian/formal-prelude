module Prelude.Monoid where

open import Prelude.Init; open SetAsType
open import Prelude.Semigroup public

record Monoid (A : Type ℓ) : Type ℓ where
  field
    overlap ⦃ sm ⦄ : Semigroup A
    ε : A
open Monoid ⦃...⦄ public hiding (sm)

record MonoidLaws (A : Type ℓ) ⦃ _ : Monoid A ⦄ (_~_ : Rel A ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  open Alg _~_
  field ε-identity : Identity ε _◇_

  ε-identityˡ : LeftIdentity ε _◇_
  ε-identityˡ = ε-identity .proj₁

  ε-identityʳ : RightIdentity ε _◇_
  ε-identityʳ = ε-identity .proj₂
open MonoidLaws ⦃...⦄ public

MonoidLaws≡ : (A : Type ℓ) ⦃ _ : Monoid A ⦄ → Type ℓ
MonoidLaws≡ A = MonoidLaws A _≡_

private variable A : Type ℓ; B : Type ℓ′

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

  MonoidLaws-Maybe : ⦃ _ : Monoid A ⦄ → ⦃ MonoidLaws≡ A ⦄ → MonoidLaws≡ (Maybe A)
  MonoidLaws-Maybe {A = A} = record {ε-identity = p , q}
    where open Alg≡
          p = LeftIdentity ε  _◇_ ∋ λ _ → refl
          q = RightIdentity ε _◇_ ∋ λ where (just _) → refl; nothing → refl

  Monoid-× : ⦃ Monoid A ⦄ → ⦃ Monoid B ⦄ → Monoid (A × B)
  Monoid-× .ε = ε , ε

  MonoidLaws-× : ⦃ _ : Monoid A ⦄ ⦃ _ : Monoid B ⦄
               → ⦃ MonoidLaws≡ A ⦄ → ⦃ MonoidLaws≡ B ⦄
               → MonoidLaws≡ (A × B)
  MonoidLaws-× {A = A} {B = B} = record {ε-identity = p , q}
    where
      open Alg≡

      p : LeftIdentity (A × B ∋ ε)  _◇_
      p (a , b) rewrite ε-identityˡ a | ε-identityˡ b = refl

      q : RightIdentity (A × B ∋ ε) _◇_
      q (a , b) rewrite ε-identityʳ a | ε-identityʳ b = refl

-- ** nats
module _ where
  open Nat
  Monoid-ℕ-+ = Monoid ℕ ∋ λ where .ε → 0
    where instance _ = Semigroup-ℕ-+
  MonoidLaws-ℕ-+ = MonoidLaws≡ ℕ ∋ record {ε-identity = +-identityˡ , +-identityʳ}
    where instance _ = Monoid-ℕ-+

  Monoid-ℕ-* = Monoid ℕ ∋ λ where .ε → 1
    where instance _ = Semigroup-ℕ-*
  MonoidLaws-ℕ-* = MonoidLaws≡ ℕ ∋ record {ε-identity = *-identityˡ , *-identityʳ}
    where instance _ = Monoid-ℕ-*

-- ** integers
module _ where
  open Integer
  Monoid-ℤ-+ = Monoid ℤ ∋ λ where .ε → 0ℤ
    where instance _ = Semigroup-ℤ-+
  MonoidLaws-ℤ-+ = MonoidLaws≡ ℤ ∋ record {ε-identity = +-identityˡ , +-identityʳ}
    where instance _ = Monoid-ℤ-+

  Monoid-ℤ-* = Monoid ℤ ∋ λ where .ε → 1ℤ
    where instance _ = Semigroup-ℤ-*
  MonoidLaws-ℤ-* = MonoidLaws≡ ℤ ∋ record {ε-identity = *-identityˡ , *-identityʳ}
    where instance _ = Monoid-ℤ-*

-- ** maybes

just-◇ˡ : ∀ {A : Type} ⦃ _ : Monoid A ⦄ ⦃ _ : MonoidLaws≡ A ⦄ (x : A) (mx : Maybe A) →
  just x ◇ mx ≡ just (x ◇ fromMaybe ε mx)
just-◇ˡ x = λ where
  (just _) → refl
  nothing  → cong just $ sym $ ε-identityʳ x

just-◇ʳ : ∀ {A : Type} ⦃ _ : Monoid A ⦄ ⦃ _ : MonoidLaws≡ A ⦄ (x : A) (mx : Maybe A) →
  mx ◇ just x ≡ just (fromMaybe ε mx ◇ x)
just-◇ʳ x = λ where
  (just _) → refl
  nothing  → cong just $ sym $ ε-identityˡ x
