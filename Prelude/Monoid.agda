module Prelude.Monoid where

open import Prelude.Init; open SetAsType
open import Prelude.Semigroup
open import Prelude.Setoid

record Monoid (A : Type ℓ) ⦃ _ : Semigroup A ⦄ : Type ℓ where
  field ε : A
open Monoid ⦃...⦄ public

record MonoidLaws (A : Type ℓ)
  ⦃ _ : Semigroup A ⦄
  ⦃ _ : Monoid A ⦄
  ⦃ _ : ISetoid A ⦄
  : Type (ℓ ⊔ₗ relℓ) where
  open Alg≈
  field ε-identity : Identity ε _◇_

  ε-identityˡ : LeftIdentity ε _◇_
  ε-identityˡ = ε-identity .proj₁

  ε-identityʳ : RightIdentity ε _◇_
  ε-identityʳ = ε-identity .proj₂
open MonoidLaws ⦃...⦄ public

private variable A : Type ℓ; B : Type ℓ′

-- specialize to propositional equality _≡_
module _ where
  instance _ = mkISetoid≡; _ = mkSetoidLaws≡

  MonoidLaws≡ : (A : Type ℓ) ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ → Type ℓ
  MonoidLaws≡ A = MonoidLaws A

  module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ ⦃ _ : MonoidLaws≡ A ⦄ where
    open MonoidLaws it public
      renaming ( ε-identity to ε-identity≡
               ; ε-identityˡ to ε-identityˡ≡; ε-identityʳ to ε-identityʳ≡
               )

module _ (A : Type ℓ) ⦃ _ : Semigroup A ⦄ where
  record LawfulMonoid ⦃ _ : LawfulSetoid A ⦄ : Typeω where
    field ⦃ is ⦄ : Monoid A
          ⦃ obeys ⦄ : MonoidLaws A
  open LawfulMonoid ⦃...⦄ using () public

  record LawfulMonoid≡ : Typeω where
    field ⦃ is ⦄ : Monoid A
          ⦃ obeys ⦄ : MonoidLaws≡ A
  open LawfulMonoid≡ ⦃...⦄ using () public

module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ where instance
  mkLawful-Monoid : ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
    → ⦃ MonoidLaws A ⦄ → LawfulMonoid A
  mkLawful-Monoid = record {}

  mkLawful-Monoid≡ : ⦃ MonoidLaws≡ A ⦄ → LawfulMonoid≡ A
  mkLawful-Monoid≡ = record {}

instance
  Monoid-List : Monoid (List A)
  Monoid-List .ε = []

  MonoidLaws-List : MonoidLaws≡ (List A)
  MonoidLaws-List = record {ε-identity = L.++-identityˡ , L.++-identityʳ}

  Monoid-Vec : Monoid (∃ (Vec A))
  Monoid-Vec .ε = 0 , []

  Monoid-String : Monoid String
  Monoid-String .ε = ""

module _ ⦃ _ : Semigroup A ⦄ where instance
  Monoid-Maybe : ⦃ Monoid A ⦄ → Monoid (Maybe A)
  Monoid-Maybe .ε = nothing

  MonoidLaws-Maybe : ⦃ _ : Monoid A ⦄ → ⦃ MonoidLaws≡ A ⦄ → MonoidLaws≡ (Maybe A)
  MonoidLaws-Maybe = record {ε-identity = p , q}
    where open Alg≡
          p = LeftIdentity ε  _◇_ ∋ λ _ → refl
          q = RightIdentity ε _◇_ ∋ λ where (just _) → refl; nothing → refl

module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Semigroup B ⦄ where instance
  Monoid-× : ⦃ Monoid A ⦄ → ⦃ Monoid B ⦄ → Monoid (A × B)
  Monoid-× .ε = ε , ε

  MonoidLaws-× : ⦃ _ : Monoid A ⦄ ⦃ _ : Monoid B ⦄
               → ⦃ MonoidLaws≡ A ⦄ → ⦃ MonoidLaws≡ B ⦄
               → MonoidLaws≡ (A × B)
  MonoidLaws-× = record {ε-identity = p , q}
    where
      open Alg≡

      p : LeftIdentity (A × B ∋ ε)  _◇_
      p (a , b) rewrite ε-identityˡ≡ a | ε-identityˡ≡ b = refl

      q : RightIdentity (A × B ∋ ε) _◇_
      q (a , b) rewrite ε-identityʳ≡ a | ε-identityʳ≡ b = refl

instance _ = mkISetoid≡; _ = mkSetoidLaws≡

-- ** nats
module _ where
  open Nat
  module _ where
    instance _ = Semigroup-ℕ-+
    Monoid-ℕ-+ = Monoid ℕ ∋ λ where .ε → 0
    instance _ = Monoid-ℕ-+
    MonoidLaws-ℕ-+ = MonoidLaws≡ ℕ ∋ record {ε-identity = +-identityˡ , +-identityʳ}
  module _ where
    instance _ = Semigroup-ℕ-*
    Monoid-ℕ-* = Monoid ℕ ∋ λ where .ε → 1
    instance _ = Monoid-ℕ-*
    MonoidLaws-ℕ-* = MonoidLaws≡ ℕ ∋ record {ε-identity = *-identityˡ , *-identityʳ}

-- ** integers
module _ where
  open Integer
  module _ where
    instance _ = Semigroup-ℤ-+
    Monoid-ℤ-+ = Monoid ℤ ∋ λ where .ε → 0ℤ
    instance _ = Monoid-ℤ-+
    MonoidLaws-ℤ-+ = MonoidLaws≡ ℤ ∋ record {ε-identity = +-identityˡ , +-identityʳ}
  module _ where
    instance _ = Semigroup-ℤ-*
    Monoid-ℤ-* = Monoid ℤ ∋ λ where .ε → 1ℤ
    instance _ = Monoid-ℤ-*
    MonoidLaws-ℤ-* = MonoidLaws≡ ℤ ∋ record {ε-identity = *-identityˡ , *-identityʳ}

-- ** maybes
module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ ⦃ _ : MonoidLaws≡ A ⦄ (x : A) where
  just-◇ˡ : ∀ (mx : Maybe A) →
    just x ◇ mx ≡ just (x ◇ fromMaybe ε mx)
  just-◇ˡ = λ where
    (just _) → refl
    nothing  → cong just $ sym $ ε-identityʳ x

  just-◇ʳ : ∀ (mx : Maybe A) →
    mx ◇ just x ≡ just (fromMaybe ε mx ◇ x)
  just-◇ʳ = λ where
    (just _) → refl
    nothing  → cong just $ sym $ ε-identityˡ x
