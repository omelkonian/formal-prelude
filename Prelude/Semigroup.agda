{-# OPTIONS --safe #-}
module Prelude.Semigroup where

open import Prelude.Init; open SetAsType
open import Prelude.Functor
open import Prelude.Setoid
open import Prelude.Lift

record Semigroup (A : Type ℓ) : Type ℓ where
  infixr 5 _◇_ _<>_
  field _◇_ : A → A → A
  _<>_ = _◇_
open Semigroup ⦃...⦄ public

record SemigroupLaws (A : Type ℓ)
  ⦃ _ : Semigroup A ⦄
  -- ⦃ _ : LawfulSetoid A ⦄
  ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
  : Type (ℓ ⊔ₗ relℓ) where
  open Alg≈
  field ◇-comm   : Commutative _◇_
        ◇-assocʳ : Associative _◇_
  ◇-assocˡ : ∀ (x y z : A) → (x ◇ (y ◇ z)) ≈ ((x ◇ y) ◇ z)
  ◇-assocˡ x y z = ≈-sym (◇-assocʳ x y z)
open SemigroupLaws ⦃...⦄ public

private variable A : Type ℓ; B : Type ℓ′

-- specialize to propositional equality _≡_
module _ where
  instance _ = mkISetoid≡; _ = mkSetoidLaws≡

  SemigroupLaws≡ : (A : Type ℓ) → ⦃ _ : Semigroup A ⦄ → Type ℓ
  SemigroupLaws≡ A = SemigroupLaws A

  module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : SemigroupLaws≡ A ⦄ where
    open SemigroupLaws it public
      renaming (◇-comm to ◇-comm≡; ◇-assocʳ to ◇-assocʳ≡; ◇-assocˡ to ◇-assocˡ≡)

record LawfulSemigroup (A : Type ℓ) ⦃ _ : LawfulSetoid A ⦄ : Typeω where
  field ⦃ is ⦄ : Semigroup A
        ⦃ obeys ⦄ : SemigroupLaws A
instance
  mkLawful-Semigroup :
    ⦃ _ : LawfulSetoid A ⦄ ⦃ _ : Semigroup A ⦄
    → ⦃ SemigroupLaws A ⦄ → LawfulSemigroup A
  mkLawful-Semigroup = record {}
open LawfulSemigroup ⦃...⦄ using () public

record LawfulSemigroup≡ (A : Type ℓ) : Typeω where
  field ⦃ is ⦄ : Semigroup A
        ⦃ obeys ⦄ : SemigroupLaws≡ A
instance
  mkLawful-Semigroup≡ : ⦃ _ : Semigroup A ⦄ → ⦃ SemigroupLaws≡ A ⦄ → LawfulSemigroup≡ A
  mkLawful-Semigroup≡ = record {}
open LawfulSemigroup≡ ⦃...⦄ using () public

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


module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Semigroup B ⦄ where instance
  Semigroup-× : Semigroup (A × B)
  Semigroup-× ._◇_ (a , b) (a′ , b′) = (a ◇ a′ , b ◇ b′)

  SemigroupLaws-× : ⦃ SemigroupLaws≡ A ⦄ → ⦃ SemigroupLaws≡ B ⦄
                  → SemigroupLaws≡ (A × B)
  SemigroupLaws-× = record {◇-assocʳ = p; ◇-comm = q}
    where
      open Alg≡

      p : Associative (_◇_ {A = A × B})
      p (a , b) (c , d) (e , f) rewrite ◇-assocʳ≡ a c e | ◇-assocʳ≡ b d f = refl

      q : Commutative (_◇_ {A = A × B})
      q (a , b) (c , d) rewrite ◇-comm≡ a c | ◇-comm≡ b d = refl


module _ where instance
  open import Prelude.Setoid.Maybe

  Semigroup-Maybe : ⦃ Semigroup A ⦄ → Semigroup (Maybe A)
  Semigroup-Maybe ._◇_ = λ where
    (just x) (just y) → just (x ◇ y)
    (just x) nothing  → just x
    nothing  m        → m

  SemigroupLaws≡-Maybe : ⦃ _ : Semigroup A ⦄ ⦃ _ : SemigroupLaws≡ A ⦄
    → SemigroupLaws≡ (Maybe A)
  SemigroupLaws≡-Maybe = record
    { ◇-assocʳ = λ where
        (just x) (just y) (just z) → cong just $ ◇-assocʳ≡ x y z
        (just x) (just y) nothing  → refl
        (just x) nothing  z        → refl
        nothing  (just y) z        → refl
        nothing  nothing  z        → refl
    ; ◇-comm = λ where
        (just x) (just y) → cong just $ ◇-comm≡ x y
        (just x) nothing  → refl
        nothing  (just y) → refl
        nothing  nothing  → it
    }

  SemigroupLaws-Maybe :
    -- ⦃ _ : LawfulSetoid A ⦄
    ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
    ⦃ _ : LawfulSemigroup A ⦄
    → SemigroupLaws (Maybe A)
  SemigroupLaws-Maybe = record
    { ◇-assocʳ = λ where
        (just x) (just y) (just z) → ◇-assocʳ x y z
        (just x) (just y) nothing  → ≈-refl {x = x ◇ y}
        (just x) nothing  z        → ≈-refl {x = just x ◇ z}
        nothing  (just y) z        → ≈-refl {x = just y ◇ z}
        nothing  nothing  z        → ≈-refl {x = z}
    ; ◇-comm = λ where
        (just x) (just y) → ◇-comm x y
        (just x) nothing  → ≈-refl {x = x}
        nothing  (just y) → ≈-refl {x = y}
        nothing  nothing  → it
    }

instance _ = mkISetoid≡; _ = mkSetoidLaws≡

-- ** nats
module _ where
  open Nat

  Semigroup-ℕ-+ = Semigroup ℕ ∋ λ where ._◇_ → _+_
  -- AssocSemigroup-ℕ-+ = AssociativeSemigroup ℕ _≡_ ∋ record {◇-assocʳ = +-assoc}
  --   where instance _ = Semigroup-ℕ-+
  -- CommSemigroup-ℕ-+ = CommutativeSemigroup ℕ _≡_ ∋ record {◇-comm = +-comm}
  --   where instance _ = Semigroup-ℕ-+
  SemigroupLaws-ℕ-+ = SemigroupLaws ℕ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℕ-+

  Semigroup-ℕ-* = Semigroup ℕ ∋ λ where ._◇_ → _*_
  -- AssocSemigroup-ℕ-* = AssociativeSemigroup ℕ _≡_ ∋ record {◇-assocʳ = *-assoc}
  --   where instance _ = Semigroup-ℕ-*
  -- CommSemigroup-ℕ-* = CommutativeSemigroup ℕ _≡_ ∋ record {◇-comm = *-comm}
  --   where instance _ = Semigroup-ℕ-*
  SemigroupLaws-ℕ-* = SemigroupLaws ℕ ∋ record {◇-assocʳ = *-assoc; ◇-comm = *-comm}
    where instance _ = Semigroup-ℕ-*

-- ** integers
module _ where
  open Integer

  Semigroup-ℤ-+ = Semigroup ℤ ∋ λ where ._◇_ → Integer._+_
  SemigroupLaws-ℤ-+ = SemigroupLaws ℤ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℤ-+

  Semigroup-ℤ-* = Semigroup ℤ ∋ λ where ._◇_ → Integer._*_
  SemigroupLaws-ℤ-* = SemigroupLaws ℤ ∋
    record {◇-assocʳ = *-assoc; ◇-comm = *-comm}
    where instance _ = Semigroup-ℤ-*
