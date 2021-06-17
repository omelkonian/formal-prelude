module Prelude.Membership where

open import Prelude.Init
open import Prelude.Functor
open import Prelude.DecEq
import Data.List.Membership.DecPropositional as DL
import Data.Vec.Membership.DecPropositional as DV

private
  variable
    A : Set ℓ₁
    B : Set ℓ₂
    n : ℕ

record HasMembership (F : Set ℓ → Set ℓ) : Set (lsuc $ lsuc ℓ) where
  infix 4 _∈_ _∉_ _∈?_ _∉?_
  field
    _∈_ : A → F A → Set ℓ
    _∈?_ : ⦃ DecEq A ⦄ → Decidable² {A = A} _∈_

  _∉_ : A → F A → Set ℓ
  x ∉ xs = ¬ x ∈ xs

  _∉?_ : ⦃ _ : DecEq A ⦄ → Decidable² {A = A} _∉_
  x ∉? xs = ¬? (x ∈? xs)

open HasMembership ⦃ ... ⦄ public

instance
  M-List : HasMembership {ℓ} List
  M-List = record { L.Mem; _∈?_ = DL._∈?_ _≟_ }

  M-Vec : HasMembership {ℓ} (flip Vec n)
  -- M-Vec = record { V.Mem }
  M-Vec ._∈_ = λ x → V.Mem._∈_ x
  M-Vec ._∈?_ {A} ⦃ _ ⦄ = λ x → DV._∈?_ _≟_ x

  M-List⁺ : HasMembership {ℓ} List⁺
  M-List⁺ ._∈_ x xs = x ∈ L.NE.toList xs
  M-List⁺ ._∈?_ x xs = x ∈? L.NE.toList xs

  M-Maybe : HasMembership {ℓ} Maybe
  M-Maybe ._∈_ x mx = M.Any.Any (_≡ x) mx
  M-Maybe ._∈?_ x mx = M.Any.dec (_≟ x) mx

record Functor∈ (F : Set ℓ → Set ℓ) ⦃ _ : HasMembership F ⦄ : Set (lsuc ℓ) where
  field
    mapWith∈ : ∀ {A B : Set ℓ} → (xs : F A) → (∀ {x : A} → x ∈ xs → B) → F B

open Functor∈ ⦃ ... ⦄ public

instance
  F∈-List : Functor∈ {ℓ} List
  F∈-List = record { L.Mem }

  F∈-List⁺ : Functor∈ {ℓ} List⁺
  F∈-List⁺ {ℓ} .mapWith∈ {A}{B} (x ∷ xs) f = f {x} (here refl) ∷ mapWith∈ xs (f ∘ there)

private
  open import Prelude.Nary
  open import Prelude.ToN

  _ : mapWith∈ (List ℕ ∋ ⟦ 10 , 20 , 30 ⟧) (toℕ ∘ L.Any.index) ≡ ⟦ 0 , 1 , 2 ⟧
  _ = refl
