------------------------------------------------------------------------
-- Enumerable types with a (finite) list witness.
------------------------------------------------------------------------

module Prelude.Enumerable where

open import Prelude.Init
open import Prelude.Nary
open import Prelude.Lists
open import Prelude.Decidable
open import Prelude.DecEq

open import Relation.Binary.PropositionalEquality using (setoid)
open import Data.List.Relation.Unary.Enumerates.Setoid using (IsEnumeration)

private variable
  a b : Level
  A : Set a
  B : Set b

IsEnumeration≡ : Pred (List A) _
IsEnumeration≡ {A = A} = IsEnumeration (setoid A)

module EnumerableProperties where
  open import Data.List.Relation.Unary.Enumerates.Setoid.Properties public

record Enumerable (A : Set ℓ) : Set ℓ where
  field witness : List A
        finite  : IsEnumeration≡ witness
open Enumerable ⦃...⦄ public

instance
  Enumerable-⊤ : Enumerable ⊤
  Enumerable-⊤ .witness = [ tt ]
  Enumerable-⊤ .finite  = λ tt → auto

  Enumerable-⊥ : Enumerable ⊥
  Enumerable-⊥ .witness = []
  Enumerable-⊥ .finite  = λ ()

  Enumerable-Bool : Enumerable Bool
  Enumerable-Bool .witness = ⟦ true , false ⟧
  Enumerable-Bool .finite  = λ{ true → auto; false → auto }

  Enumerable-× : ⦃ Enumerable A ⦄ → ⦃ Enumerable B ⦄ → Enumerable (A × B)
  Enumerable-× .witness = cartesianProduct witness witness
  Enumerable-× .finite  = λ where (x , y) → cartesianProduct-∈ (finite x) (finite y)

All⇒∀ : ⦃ _ : Enumerable A ⦄ {P : Pred₀ A} → All P witness → (∀ x → P x)
All⇒∀ allP x = L.All.lookup allP (finite x)
