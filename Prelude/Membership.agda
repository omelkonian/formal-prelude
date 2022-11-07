module Prelude.Membership where

open import Prelude.Init; open SetAsType
open import Prelude.Functor
open import Prelude.DecEq
import Data.List.Membership.DecPropositional as DL
import Data.Vec.Membership.DecPropositional as DV

private
  variable
    A : Type ℓ₁
    B : Type ℓ₂
    n : ℕ

record HasMembership (F : Type ℓ → Type ℓ) : Type (lsuc $ lsuc ℓ) where
  infix 4 _∈_ _∉_ _∈?_
  field
    _∈_ : A → F A → Type ℓ
    _∈?_ : ⦃ DecEq A ⦄ → Decidable² {A = A} _∈_

  _∉_ : A → F A → Type ℓ
  _∉_ = ¬_ ∘₂ _∈_

  module _ {A} ⦃ _ : DecEq A ⦄ where
    infix 4 _∉?_ _∈ᵇ_ _∉ᵇ_

    _∉?_ : Decidable² {A = A} _∉_
    _∉?_ = ¬? ∘₂ _∈?_

    _∈ᵇ_ _∉ᵇ_ : A → F A → Bool
    _∈ᵇ_ = isYes ∘₂ _∈?_
    _∉ᵇ_ = isYes ∘₂ _∉?_

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

record Functor∈ (F : Type ℓ → Type ℓ) ⦃ _ : HasMembership F ⦄ : Type (lsuc ℓ) where
  field
    mapWith∈ : ∀ {A B : Type ℓ} → (xs : F A) → (∀ {x : A} → x ∈ xs → B) → F B

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

module _ {A B : Type} (f : A → B) where
  ∈⁺-map⁺ : ∀ {x xs} → x ∈ xs → f x ∈ L.NE.map f xs
  ∈⁺-map⁺ = L.Mem.∈-map⁺ f

  ∈⁺-map⁻ : ∀ {y xs} → y ∈ L.NE.map f xs → ∃ λ x → x ∈ xs × y ≡ f x
  ∈⁺-map⁻ = L.Mem.∈-map⁻ f
