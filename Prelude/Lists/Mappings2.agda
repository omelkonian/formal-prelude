------------------------------------------------------------------------
-- Mappings as total functions from membership proofs of a finite list.

module Prelude.Lists.Mappings2 where

open import Prelude.Init; open SetAsType
open import Prelude.InferenceRules
open import Prelude.Lists.Membership
open import Prelude.Lists.Mappings

private variable
  a b p : Level
  A : Type a; B : Type b
  P : Pred A p

  x : A
  xs xs′ ys zs : List A

Unique⇒weaken≗ : ∀ (f : xs ↦′ P) (p p′ : ys ⊆ xs) →
  Unique xs
  ─────────────────────────────
  weaken-↦ f p ≗↦ weaken-↦ f p′
Unique⇒weaken≗ f p p′ uniq x∈ =
  cong f $ ∈-irr uniq (p x∈) (p′ x∈)
