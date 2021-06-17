module Prelude.TestOrd where

open import Prelude.Init hiding (_≤_; _≤?_; _≥_; _≥?_)
open import Prelude.Ord

∀≤max′ : ∀ t (ts : List ℕ) → t ≤ maximum t ts
∀≤max′ t [] = Nat.≤-refl
∀≤max′ t (t′ ∷ ts)
  with t′ ≤? t
... | yes t′≤ = {!Nat.≤-trans t′≤!}
... | no  t′> = ∀≤max′ t ts

∀≤max : ∀ t₀ (ts : List ℕ) → All (_≤ maximum t₀ ts) ts
∀≤max t₀ [] = []
∀≤max t₀ (t ∷ ts)
  with t ≤? t₀
... | yes t≤ = qed ∷ ∀≤max t ts
  where
    qed : t ≤ maximum t ts
    qed = ∀≤max′ t ts
... | no  t> = qed ∷ ∀≤max t₀ ts
  where
    qed : t ≤ maximum t₀ ts
    qed = {!!}


{-

  maximum 0 (t ∷ ts)
≡ foldl max   0     (t ∷ ts)
         c    n      x   xs
  foldl  c  (c n x) ts
  foldl max (0 `max` t) ts
≡ foldl max (0 `max` t) ts


-}
