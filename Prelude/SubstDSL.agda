module Prelude.SubstDSL where

open import Prelude.Init; open SetAsType

private variable
  A : Type ℓ
  x y : A

-- forward
substˡ = subst
substˡ′ = substˡ
infixl 4 substˡ″
substˡ″ : {P : Pred₀ A} → x ≡ y → P x → P y
substˡ″ = substˡ _
syntax substˡ  (λ ◆ → P) eq p = p :~ eq ⟪ ◆ ∣ P ⟫
syntax substˡ′ P         eq p = p :~ eq ⟪ P ⟫
syntax substˡ″           eq p = p :~ eq

-- backward
substʳ : (P : Pred₀ A) → y ≡ x → P x → P y
substʳ P eq p = subst P (sym eq) p
substʳ′ = substʳ
substʳ″ : {P : Pred₀ A} → y ≡ x → P x → P y
substʳ″ = substʳ _
infixl 4 substʳ″
syntax substʳ  (λ ◆ → P) eq p = ⟪ ◆ ∣ P ⟫ eq ~: p
syntax substʳ′ P         eq p =     ⟪ P ⟫ eq ~: p
syntax substʳ″           eq p =           eq ~: p

-- [T0D0] macro that automagically finds which context P to use

private
  postulate
    n m : ℕ
    n≡m : n ≡ m
    P : Pred₀ ℕ
    pₙ : P n
    pₘ : P m
    p : P m × P n
    p₇ : P 7

  -- backward
  _ : P n
  _ = ⟪ P ⟫ n≡m ~: pₘ

  -- forward
  _ : P m
  _ = pₙ :~ n≡m ⟪ P ⟫

  open Nat

  -- backward chain
  _ : P (n + 0) × P (0 + m)
  _ = ⟪ ◆ ∣ P ◆ × P (0 + m) ⟫ +-identityʳ _ ~:
      ⟪ ◆ ∣ P ◆ × P (0 + m) ⟫ n≡m           ~:
      ⟪ ◆ ∣ P m × P ◆       ⟫ +-identityˡ _ ~:
      ⟪ ◆ ∣ P m × P ◆       ⟫ sym n≡m       ~: p

  -- forward chain
  _ : P (n + 0) × P (0 + m)
  _ = p :~ n≡m                 ⟪ ◆ ∣ P m × P ◆       ⟫
        :~ sym (+-identityˡ _) ⟪ ◆ ∣ P m × P ◆       ⟫
        :~ sym n≡m             ⟪ ◆ ∣ P ◆ × P (0 + m) ⟫
        :~ sym (+-identityʳ _) ⟪ ◆ ∣ P ◆ × P (0 + m) ⟫
