module Prelude.Coercions where

open import Prelude.Init
open import Prelude.General

infix -1 _↝_
record _↝_ (A B : Set) : Set where
  field to : A → B
  -- syntax to {A}{B} x = [ A ∋ x ]↝ B
  syntax to {B = B} = to[ B ]
open _↝_ ⦃...⦄ public

private variable A B : Set

tos : ⦃ A ↝ B ⦄ → List A ↝ List B
tos .to = map to

instance
  ↝×↜⇒↔ : ⦃ A ↝ B ⦄ → ⦃ B ↝ A ⦄ → A ↔ B
  ↝×↜⇒↔ = to , to

private
  𝟚 = ⊤ ⊎ ⊤
  pattern 𝕃 = inj₁ tt; pattern ℝ = inj₂ tt

  instance
    ↝Bool : ⊤ ⊎ ⊤ ↝ Bool
    ↝Bool .to = λ where
      𝕃 → true
      ℝ → false

    Bool↝ : Bool ↝ ⊤ ⊎ ⊤
    Bool↝ .to = λ where
      true  → 𝕃
      false → ℝ

  _ : Bool
  _ = to 𝕃

  _ : 𝟚
  _ = to true

  _ : Bool → Bool
  _ = not ∘ to[ Bool ] ∘ to[ 𝟚 ]

  _ : 𝟚 ↔ Bool
  _ = it
