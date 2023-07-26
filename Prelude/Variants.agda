-------------------------------------------------------------------------------------
-- Typeclass-based approach to implicit sums/variants.
-- We only give two instances: the left and right injection.
--
-- The usecase is having arguments that can be elements of any of two types.
-------------------------------------------------------------------------------------
module Prelude.Variants where

open import Prelude.Init; open SetAsType

private pattern 𝕃 = inj₁ refl; pattern ℝ = inj₂ refl

record _∣_ (A B X : Type) : Type₁ where
  field X≡ : (X ≡ A) ⊎ (X ≡ B)
  syntax X≡ {A}{B}{X} = ⟨ A ⊎? B ⟩ X

  to : X → A ⊎ B
  to with X≡
  ... | 𝕃 = inj₁
  ... | ℝ = inj₂
  syntax to {A = A} {B = B} = to⟨ A ⊎? B ⟩
open _∣_ ⦃...⦄ public

private variable X Y : Type

instance
  Pick𝕃 : (X ∣ Y) X
  Pick𝕃 = record {X≡ = 𝕃}

  Pickℝ : (X ∣ Y) Y
  Pickℝ = record {X≡ = ℝ}

open import Prelude.Show

test-variant : ⦃ (ℕ ∣ String) X ⦄ → X → String
test-variant {X = X} with ⟨ ℕ ⊎? String ⟩ X
... | 𝕃 = show
... | ℝ = id
-- test-variant x with to⟨ ℕ ⊎? String ⟩ x
-- ... | inj₁ n = show n
-- ... | inj₂ s = s
