module Prelude.Semigroup where

open import Prelude.Init; open SetAsType
open import Prelude.Functor

record Semigroup (A : Type ℓ) : Type ℓ where
  infixr 5 _◇_ _<>_
  field _◇_ : A → A → A
  _<>_ = _◇_
open Semigroup ⦃...⦄ public

record SemigroupLaws (A : Type ℓ) ⦃ _ : Semigroup A ⦄ (_≈_ : Rel A ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  open Alg _≈_
  field
    -- doesn't work when you have multiple laws simultaneously
    -- overlap ⦃ sm ⦄ : Semigroup A
    ◇-comm   : Commutative _◇_
    ◇-assocʳ : Associative _◇_
open SemigroupLaws ⦃...⦄ public

SemigroupLaws≡ : (A : Type ℓ) ⦃ _ : Semigroup A ⦄ → Type ℓ
SemigroupLaws≡ A = SemigroupLaws A _≡_

private variable A : Type ℓ

module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : SemigroupLaws≡ A ⦄ where
  ◇-assocˡ : ∀ (x y z : A) → (x ◇ (y ◇ z)) ≡ ((x ◇ y) ◇ z)
  ◇-assocˡ x y z = sym (◇-assocʳ x y z)

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

  Semigroup-Maybe : ⦃ Semigroup A ⦄ → Semigroup (Maybe A)
  Semigroup-Maybe ._◇_ = λ where
    (just x) (just y) → just (x ◇ y)
    (just x) nothing  → just x
    nothing  m        → m

  SemigroupLaws-Maybe : ⦃ sm : Semigroup A ⦄ → ⦃ SemigroupLaws≡ A ⦄ → SemigroupLaws≡ (Maybe A)
  SemigroupLaws-Maybe {A = A} = record {◇-assocʳ = p; ◇-comm = q}
    where
      open Alg≡

      p : Associative (_◇_ {A = Maybe A})
      p (just _) (just _) (just _) = cong just (◇-assocʳ _ _ _)
      p (just _) (just _) nothing  = refl
      p (just _) nothing  _ = refl
      p nothing  (just _) _ = refl
      p nothing  nothing  _ = refl

      q : Commutative (_◇_ {A = Maybe A})
      q (just x) (just y) = cong just (◇-comm x y)
      q (just _) nothing  = refl
      q nothing  (just _) = refl
      q nothing  nothing  = refl


-- ** nats
module _ where
  open Nat

  Semigroup-ℕ-+ = Semigroup ℕ ∋ λ where ._◇_ → _+_
  -- AssocSemigroup-ℕ-+ = AssociativeSemigroup ℕ _≡_ ∋ record {◇-assocʳ = +-assoc}
  --   where instance _ = Semigroup-ℕ-+
  -- CommSemigroup-ℕ-+ = CommutativeSemigroup ℕ _≡_ ∋ record {◇-comm = +-comm}
  --   where instance _ = Semigroup-ℕ-+
  SemigroupLaws-ℕ-+ = SemigroupLaws ℕ _≡_ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℕ-+

  Semigroup-ℕ-* = Semigroup ℕ ∋ λ where ._◇_ → _*_
  -- AssocSemigroup-ℕ-* = AssociativeSemigroup ℕ _≡_ ∋ record {◇-assocʳ = *-assoc}
  --   where instance _ = Semigroup-ℕ-*
  -- CommSemigroup-ℕ-* = CommutativeSemigroup ℕ _≡_ ∋ record {◇-comm = *-comm}
  --   where instance _ = Semigroup-ℕ-*
  SemigroupLaws-ℕ-* = SemigroupLaws ℕ _≡_ ∋
    record {◇-assocʳ = *-assoc; ◇-comm = *-comm}
    where instance _ = Semigroup-ℕ-*

-- ** integers
module _ where
  open Integer

  Semigroup-ℤ-+ = Semigroup ℤ ∋ λ where ._◇_ → Integer._+_
  SemigroupLaws-ℤ-+ = SemigroupLaws ℤ _≡_ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℤ-+

  Semigroup-ℤ-* = Semigroup ℤ ∋ λ where ._◇_ → Integer._*_
  SemigroupLaws-ℤ-* = SemigroupLaws ℤ _≡_ ∋
    record {◇-assocʳ = *-assoc; ◇-comm = *-comm}
    where instance _ = Semigroup-ℤ-*
