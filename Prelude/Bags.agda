open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Nary

module Prelude.Bags {A : Set} where

open import Prelude.Bags.Interface      -- abstract interface
import Prelude.Bags.AsUniqueLists as S₁ -- \ implementations
import Prelude.Bags.AsPredicates  as S₂ -- /
module Imp = S₁                         -- pick implementation

open import Prelude.DecEq
open import Prelude.Membership

module _ ⦃ _ : DecEq A ⦄ where
  private S = Bagᴵ A _ ∋ record {Imp}
  instance _ = S; open Bagᴵ S public
  open DecBagᴵ   {A = A} record {Imp} public
  open ListBagᴵ  {A = A} record {Imp} public
  open DecEqBagᴵ {A = A} record {Imp} public

  _ : Set'
  _ = singleton x ∪ singleton y ─ fromList ⟦ x , y , x , y ⟧
    where postulate x y : A
