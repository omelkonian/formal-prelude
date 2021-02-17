module Prelude.Sets.Example where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Nary

{-
open import Prelude.Semigroup
open import Prelude.PointedFunctor

instance
  Semigroup-Set' : ∀ {A} ⦃ _ : DecEq A ⦄ → Semigroup Set⟨ A ⟩
  Semigroup-Set' ._◇_ = _∪_

  -- PFunctor-Set' : PointedFunctor λ A ⦃ _ : DecEq A ⦄ → Set⟨ A ⟩
  -- PFunctor-Set' .point = singleton
-}

_ : Set⟨ ℕ ⟩
_ = singleton 5 ∪ singleton 10

test-deceq : Set⟨ ℕ ⟩ → Set⟨ ℕ ⟩ → Bool
test-deceq x y with x ≟ y
... | yes _ = true
... | no  _ = false
