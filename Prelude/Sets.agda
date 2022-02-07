open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Nary

module Prelude.Sets {A : Set} where

open import Prelude.Sets.Interface      -- abstract interface
import Prelude.Sets.AsUniqueLists as S₁ -- \ implementations
import Prelude.Sets.AsPredicates  as S₂ -- /
module Imp = S₁                         -- pick implementation

open import Prelude.DecEq
open import Prelude.Membership

module _ ⦃ _ : DecEq A ⦄ where
  private S = Setᴵ A _ ∋ record {Imp}
  instance _ = S; open Setᴵ S public
  open DecSetᴵ   {A = A} record {Imp} public
  open ListSetᴵ  {A = A} record {Imp} public
  open DecEqSetᴵ {A = A} record {Imp} public

  _ : Set'
  _ = singleton x ∪ singleton y ─ fromList ⟦ x , y , x , y ⟧
    where postulate x y : A
