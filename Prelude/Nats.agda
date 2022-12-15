------------------------------------------------------------------------
-- Utilities for natural numbers.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Prelude.Nats where

open import Prelude.Init; open SetAsType
open Nat

∸-suc : ∀ m n → n ≤ m → suc (m ∸ n) ≡ suc m ∸ n
∸-suc zero    zero    _         = refl
∸-suc (suc m) zero    _         = refl
∸-suc (suc m) (suc n) (s≤s n≤m) = ∸-suc m n n≤m

∸-∸-comm : ∀ m n o → (m ∸ n) ∸ o ≡ (m ∸ o) ∸ n
∸-∸-comm m n o rewrite Nat.∸-+-assoc m n o | Nat.+-comm n o | Nat.∸-+-assoc m o n = refl

+-reassoc : ∀ m n o → m + (n + o) ≡ n + (o + m)
+-reassoc m n o =
  begin
    m + (n + o)
  ≡⟨ Nat.+-comm m (n + o) ⟩
    (n + o) + m
  ≡⟨ Nat.+-assoc n o m ⟩
    n + (o + m)
  ∎ where open ≡-Reasoning

+-reassoc˘ : ∀ m n o → m + (n + o) ≡ n + (m + o)
+-reassoc˘ m n o =
  begin
    m + (n + o)
  ≡⟨ sym $ Nat.+-assoc m n o ⟩
    (m + n) + o
  ≡⟨ cong (_+ o) $ Nat.+-comm m n ⟩
    (n + m) + o
  ≡⟨ Nat.+-assoc n m o ⟩
    n + (m + o)
  ∎ where open ≡-Reasoning

∸-∸-assoc : ∀ m n o → n < m → o ≤ n → m ∸ (n ∸ o) ≡ (m ∸ n) + o
∸-∸-assoc m _       zero    _     _       = sym $ Nat.+-identityʳ _
∸-∸-assoc m (suc n) (suc o) 1+n<m (s≤s p)
  with n<m ← ≤-trans Nat.pred[n]≤n 1+n<m
  rewrite ∸-∸-assoc m n o n<m p | Nat.+-suc (m ∸ suc n) o =
  begin
    m ∸ n + o
  ≡⟨ cong (_+ o) $ sym $ Nat.suc[pred[n]]≡n $ Nat.m>n⇒m∸n≢0 n<m ⟩
    suc (Nat.pred (m ∸ n)) + o
  ≡⟨ cong (λ ◆ → suc (◆ + o)) $ Nat.pred[m∸n]≡m∸[1+n] m n ⟩
    suc (m ∸ suc n + o)
  ∎ where open ≡-Reasoning

x+y+0≡y+x+0 : ∀ x y → x + (y + 0) ≡ (y + x) + 0
x+y+0≡y+x+0 x y rewrite sym (+-assoc x y 0) | +-comm x y = refl

1+[m∸[1+n]]≡m∸n : ∀ m n → n < m → suc (m ∸ suc n) ≡ m ∸ n
1+[m∸[1+n]]≡m∸n m n = sym ∘ Nat.+-∸-assoc 1

m+z∸n+z≡m∸n : ∀ m n z → (m + z) ∸ (n + z) ≡ m ∸ n
m+z∸n+z≡m∸n m n zero rewrite Nat.+-identityʳ m | Nat.+-identityʳ n = refl
m+z∸n+z≡m∸n m n (suc z) rewrite Nat.+-suc m z | Nat.+-suc n z = m+z∸n+z≡m∸n m n z
m∸[z+o]∸n∸[w+o]≡[m∸z]∸[n∸w] : ∀ m n z o w → o ≤ n ∸ w →
  (m ∸ (z + o)) ∸ (n ∸ (w + o)) ≡ (m ∸ z) ∸ (n ∸ w)
m∸[z+o]∸n∸[w+o]≡[m∸z]∸[n∸w] m n z o w o≤
  rewrite sym $ Nat.∸-+-assoc m z o | sym $ Nat.∸-+-assoc n w o
  = begin
    (m ∸ z ∸ o) ∸ (n ∸ w ∸ o)
  ≡⟨⟩
    ((m ∸ z) ∸ o) ∸ ((n ∸ w) ∸ o)
  ≡⟨ ∸-∸-comm (m ∸ z) o ((n ∸ w) ∸ o) ⟩
    ((m ∸ z) ∸ ((n ∸ w) ∸ o)) ∸ o
  ≡⟨ Nat.∸-+-assoc (m ∸ z) ((n ∸ w) ∸ o) o ⟩
    (m ∸ z) ∸ (((n ∸ w) ∸ o) + o)
  ≡⟨ cong ((m ∸ z) ∸_) $ Nat.m∸n+n≡m {(n ∸ w)} {o} o≤ ⟩
    (m ∸ z) ∸ (n ∸ w)
  ∎ where open ≡-Reasoning

m≡n⇒m∸n≡0 : ∀ {m n} → m ≡ n → m ∸ n ≡ 0
m≡n⇒m∸n≡0 {m}{.m} refl = Nat.n∸n≡0 m

1+n∸n≡1 : ∀ n → 1 + n ∸ n ≡ 1
1+n∸n≡1 n = trans (Nat.+-∸-assoc 1 {n = n} Nat.≤-refl) (cong suc $ Nat.n∸n≡0 n)

m≡n⇒1+m∸n≡1 : ∀ {m n} → m ≡ n → 1 + m ∸ n ≡ 1
m≡n⇒1+m∸n≡1 {m}{.m} refl = 1+n∸n≡1 m

≥-trans : Transitive _≥_
≥-trans x≥y y≥z = ≤-trans y≥z x≥y
