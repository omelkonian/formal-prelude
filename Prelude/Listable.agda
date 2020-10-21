------------------------------------------------------------------------
-- Finite types with a (finite) list witness. 
------------------------------------------------------------------------
module Prelude.Listable where

open import Prelude.Init
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Nary
open import Prelude.Lists

record Listable {ℓ} (A : Set ℓ) : Set ℓ where
  field
    witness : List A
    finite  : ∀ x → x ∈ witness

open Listable {{...}} public

private
  variable
    a b : Level
    A : Set a
    B : Set b

instance
  Listable-⊤ : Listable ⊤
  Listable-⊤ .witness = [ tt ]
  Listable-⊤ .finite  = λ tt → auto

  Listable-⊥ : Listable ⊥
  Listable-⊥ .witness = []
  Listable-⊥ .finite  = λ ()

  Listable-Bool : Listable Bool
  Listable-Bool .witness = ⟦ true , false ⟧
  Listable-Bool .finite  = λ{ true → auto; false → auto }

  Listable-× : {{_ : Listable A}} {{_ : Listable B}} → Listable (A × B)
  Listable-× = record { witness = cartesianProduct witness witness
                      ; finite  = λ{ (x , y) → cartesianProduct-∈ (finite x) (finite y) } }
