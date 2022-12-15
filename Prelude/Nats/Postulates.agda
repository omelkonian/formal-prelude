-- {-# OPTIONS --safe #-}
module Prelude.Nats.Postulates where

open import Prelude.Init
open Nat

private variable m n x y z x′ y′ z′ i : ℕ

postulate
  ¬x>0⇒x≡0 : ¬ (x > 0) → x ≡ 0
  x≡0⇒¬x>0 : x ≡ 0 → ¬ (x > 0)
  x≤0⇒x≡0 : x ≤ 0 → x ≡ 0
  x>0,x≤1⇒x≡1 : x > 0 → x ≤ 1 → x ≡ 1
  ≤-+ˡ : x + y ≤ z → x ≤ z
  ≤-+ʳ : x + y ≤ z → y ≤ z
  x+y≤y⇒x≡0 : x + y ≤ y → x ≡ 0
  ¬>⇒≤ : ¬ (m > n) → m ≤ n
  x+y>x⇒y>0 : x + y > x → y > 0
  ≥-+-swapˡ : x ≥ x′ → x + y ≥ x′ + y
  ≥-+-swapʳ : ∀ {x y y′} → y ≥ y′ → x + y ≥ x + y′
  ≥-+-swapˡʳ : x ≥ x′ → y ≥ y′ → x + y ≥ x′ + y′
  ¬i≥x+y : i ≤ 1 → x > 0 → y > 0 → ¬ (i ≥ x + y)
  x<x+1 : ∀ x → x < x + 1
  +-helper : ∀ {x y z} → x ≡ y + z → y > 0 → z > 0 → (y < x) × (z < x)
  x<x+y : ∀ x → y > 0 → x < x + y
  juxtapose-+/< : x < x′ → y < y′ → x + y < x′ + y′

x≤0⇒x≡0′ : ∀ {n m} → n ≡ 0 → m ≤ n → m ≡ 0
x≤0⇒x≡0′ refl = x≤0⇒x≡0
