open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Nary

module Prelude.Sets {A : Set} where

open import Prelude.Sets.Interface
import Prelude.Sets.AsUniqueLists as S₁
import Prelude.Sets.AsPredicates  as S₂

open import Prelude.DecEq
open import Prelude.Membership

-- open Setᴵ (Setᴵ A _ ∋ record {S₂}) public
--   renaming (_≈_ to _≈ˢ_)

module _ ⦃ _ : DecEq A ⦄ where
  open Setᴵ (Setᴵ A _ ∋ record {S₁}) public
    renaming (_≈_ to _≈ˢ_)
  open DecSetᴵ (DecSetᴵ A _ ∋ record {S₁}) public
  open ListSetᴵ (ListSetᴵ A _ ∋ record {S₁}) public
  open DecEqSetᴵ (DecEqSetᴵ A _ ∋ record {S₁}) public

  _ : Set'
  _ = singleton x ∪ singleton y ─ fromList ⟦ x , y , x , y ⟧
    where postulate x y : A
