------------------------------------------------------------------------
-- General utilities
------------------------------------------------------------------------

module Prelude.General where

open import Data.Unit using (tt)
open import Data.Bool using (T; true)
open import Data.Nat  using (_+_)

open import Data.Nat.Properties using (+-assoc; +-comm)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

------------------------------------------------------------------------
-- Bools.

true⇒T : ∀ {b} → b ≡ true → T b
true⇒T refl = tt

------------------------------------------------------------------------
-- Nats.

x+y+0≡y+x+0 : ∀ x y → x + (y + 0) ≡ (y + x) + 0
x+y+0≡y+x+0 x y rewrite sym (+-assoc x y 0) | +-comm x y = refl
