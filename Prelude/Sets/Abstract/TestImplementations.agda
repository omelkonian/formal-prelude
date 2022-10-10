open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Nary

open import Prelude.Sets.Abstract.Interface      -- abstract interface
import Prelude.Sets.Abstract.AsUniqueLists as S₁ -- \ implementations
import Prelude.Sets.Abstract.AsPredicates  as S₂ -- /
module Imp = S₁                                  -- pick implementation

module Prelude.Sets.Abstract.TestImplementations {A : Set} ⦃ _ : DecEq A ⦄ where

private S = Setᴵ A _ ∋ record {Imp}
instance _ = S; open Setᴵ S public
open DecSetᴵ   {A = A} record {Imp} public
open ListSetᴵ  {A = A} record {Imp} public
open DecEqSetᴵ {A = A} record {Imp} public

_ = Set' ∋ singleton x ∪ singleton y ─ fromList ⟦ x , y , x , y ⟧
  where postulate x y : A
