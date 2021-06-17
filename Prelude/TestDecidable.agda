module Prelude.TestDecidable where

open import Prelude.Init
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Nary

_ : 1 ∈ (List ℕ ∋ ⟦ 0 , 1 , 2 ⟧)
_ = auto

_ : 3 ∉ (List ℕ ∋ ⟦ 0 , 1 , 2 ⟧)
_ = auto

f : 3 ∈ (List ℕ ∋ ⟦ 0 , 1 , 2 ⟧) → 2 ≡ 3
f p = contradict p
