module Prelude.Nary where

open import Prelude.Init
open import Prelude.General
open import Prelude.Semigroup public
open import Prelude.Applicative public

⟦_⟧ : ∀ {n A} {F : Set → Set} {{_ : Semigroup (F A)}} {{_ : Applicative F}} → A ^ n → F A
⟦_⟧ {n = zero}  x        = pure x
⟦_⟧ {n = suc n} (x , xs) = pure x ◇ ⟦ xs ⟧

_ : List ℕ
_ = ⟦ 1 , 2 , 3 , 4 ⟧

_ : List⁺ ℕ
_ = ⟦ 1 , 2 , 3 , 4 ⟧

-- _ : ∃ (Vec ℕ)
-- _ = ⟦ 1 , 2 , 3 , 4 ⟧
