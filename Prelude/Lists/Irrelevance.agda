module Prelude.Lists.Irrelevance where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Irrelevance
open import Prelude.Apartness
import Data.List.Relation.Unary.AllPairs as AP

private variable
  A : Type ℓ; B : Type ℓ′
  xs : List A; ys : List A
  p r : Level
  P : Pred A p
  R : Rel A r

instance
  ·-All : ⦃ ·¹ P ⦄ → ·¹ All P
  ·-All .∀≡ = L.All.irrelevant ∀≡

  ·-AllPairs : ⦃ ·² R ⦄ → ·¹ AllPairs R
  ·-AllPairs .∀≡ = AP.irrelevant ∀≡

-- ** irrelevant version of Data.List.Unary.Unique
private
  ·Distinct : Rel A _
  ·Distinct = ·¬_ ∘₂ _≡_

·Unique : Pred (List A) _
·Unique = AllPairs ·Distinct

private
  _ : · ·Unique xs
  _ = it

·Unique⇒Unique : ·Unique xs → Unique xs
·Unique⇒Unique = AP.map ·⊥⇒⊥

Unique⇒·Unique : Unique xs → ·Unique xs
Unique⇒·Unique = AP.map ⊥⇒·⊥

·Unique⇔Unique : ·Unique xs ↔ Unique xs
·Unique⇔Unique = ·Unique⇒Unique , Unique⇒·Unique

module _ {f : A → B} (f-inj : Injective≡ f) where
  ·Unique-map⁺ : ·Unique xs → ·Unique (map f xs)
  ·Unique-map⁺ = Unique⇒·Unique ∘ L.Uniq.map⁺ f-inj ∘ ·Unique⇒Unique

module _ (P? : Decidable¹ P) where
  ·Unique-filter⁺ : ·Unique xs → ·Unique (filter P? xs)
  ·Unique-filter⁺ = Unique⇒·Unique ∘ L.Uniq.filter⁺ P? ∘ ·Unique⇒Unique

·Unique-++⁺ : ·Unique xs → ·Unique ys → xs ♯ ys → ·Unique (xs ++ ys)
·Unique-++⁺ p q dis =
  Unique⇒·Unique $ L.Uniq.++⁺ (·Unique⇒Unique p) (·Unique⇒Unique q) dis
