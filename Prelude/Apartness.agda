{-# OPTIONS --safe #-}
module Prelude.Apartness where

open import Prelude.Init; open SetAsType
open import Prelude.ToList
open import Prelude.Decidable

record _//_ (A : Type ℓ) (B : Type ℓ′) {ℓ″} : Type (ℓ ⊔ₗ ℓ′ ⊔ₗ lsuc ℓ″) where
  infix 4 _♯_
  field _♯_ : A → B → Type ℓ″

  _♯?_ : ⦃ _ : ∀ {x y} → (x ♯ y) ⁇ ⦄ → Decidable² _♯_
  _♯?_ _ _ = dec
open _//_ ⦃...⦄ public

_//^⦅_⦆_ : ∀ (A : Type ℓ) ℓ (B : Type ℓ′) → Type _
A //^⦅ ℓ″ ⦆ B = _//_ A B {ℓ″}

private variable
  X : Type ℓ; Y : Type ℓ′; Z : Type ℓ″
  n : ℕ

-- Unit test to check support for relating types at different levels.
private module _ (X₁ : Type₁) where
  _ : ℕ // X₁
  _ = λ where ._♯_ _ → const ⊤

instance
  Apart-List : List X // List X
  Apart-List ._♯_ = Disjoint

  -- Apart-ToList : ⦃ ToList X Y ⦄ → List Y // X
  -- Apart-ToList = toList⇒//ʳ

-- do not expose as instance, as it leads to issues with instance resolution
toList⇒// : ⦃ ToList X Y ⦄ → X // X
toList⇒// ._♯_ x x′ = toList x ♯ toList x′

toList²⇒// : ⦃ ToList X Z ⦄ → ⦃ ToList Y Z ⦄ → X // Y
toList²⇒// ._♯_ x x′ = toList x ♯ toList x′

toList⇒//ˡ : ⦃ ToList X Y ⦄ → X // List Y
toList⇒//ˡ ._♯_ x ys = toList x ♯ ys

toList⇒//ʳ : ⦃ ToList X Y ⦄ → List Y // X
toList⇒//ʳ ._♯_ ys x = ys ♯ toList x

mkSym-// : ⦃ X //^⦅ ℓ″ ⦆ Y ⦄ → Y //^⦅ ℓ″ ⦆ X
mkSym-// ⦃ d ⦄ ._♯_ = flip (_♯_ ⦃ d ⦄)

instance
  Apart-List⁺ : List⁺ X // List⁺ X
  Apart-List⁺ = toList⇒//

  Apart-List⁺ʳ : List X // List⁺ X
  Apart-List⁺ʳ = toList⇒//ʳ

  Apart-List⁺ˡ : List⁺ X // List X
  Apart-List⁺ˡ = toList⇒//ˡ

  Apart-Str = String // String ∋ toList⇒//

  Apart-Vec : Vec X n // Vec X n
  Apart-Vec = toList⇒//

  Apart-Vec⁺ʳ : List X // Vec X n
  Apart-Vec⁺ʳ = toList⇒//ʳ

  Apart-Vec⁺ˡ : Vec X n // List X
  Apart-Vec⁺ˡ = toList⇒//ˡ

  Apart-List⁺-Vec : List⁺ X // Vec X n
  Apart-List⁺-Vec = toList²⇒//

  Apart-Vec-List⁺ : Vec X n // List⁺ X
  Apart-Vec-List⁺ = toList²⇒//
