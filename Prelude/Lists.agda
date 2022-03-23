------------------------------------------------------------------------
-- List utilities.
------------------------------------------------------------------------

module Prelude.Lists where

import Data.List.Relation.Binary.Pointwise as PW

open import Prelude.Init hiding (_∷ʳ_)
open Nat
open L.Mem
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Bifunctor

private variable
  a b c : Level
  A : Set a
  B : Set b
  C : Set c

  x y : A
  xs ys : List A
  xss : List (List A)

  P : Pred₀ A

open import Prelude.Lists.Core public
open import Prelude.Lists.Empty public
open import Prelude.Lists.NonEmpty public
open import Prelude.Lists.Indexed public
open import Prelude.Lists.Combinatorics public
open import Prelude.Lists.Permutations public
open import Prelude.Lists.Concat public
open import Prelude.Lists.Count public
open import Prelude.Lists.Sums public
open import Prelude.Lists.Membership public
open import Prelude.Lists.Singletons public
open import Prelude.Lists.MapMaybe public
open import Prelude.Lists.Mappings public
open import Prelude.Lists.SuffixSubset public

-- ** Prefix relation, instantiated for propositional equality.
Prefix≡ : List A → List A → Set _
Prefix≡ = Prefix _≡_

-- ** Suffix relation, instantiated for propositional equality.
Suffix≡ : List A → List A → Set _
Suffix≡ = Suffix _≡_

suffix-refl : (xs : List A) → Suffix≡ xs xs
suffix-refl xs = here (PW.≡⇒Pointwise-≡ refl)

∈⇒Suffix : {x : A} {ys : List A}
  → x ∈ ys
  → ∃[ xs ] Suffix≡ (x ∷ xs) ys
∈⇒Suffix {ys = x ∷ xs}  (here refl) = xs , here (refl ∷ PW.refl refl)
∈⇒Suffix {ys = _ ∷ ys′} (there x∈) = map₂′ there (∈⇒Suffix x∈)

postulate
  Suffix⇒⊆ : {xs ys : List A} → Suffix≡ xs ys → xs ⊆ ys

  proj₁∘∈⇒Suffix≡ : {xs : List⁺ A} {ys zs : List A} (∀x∈ : All⁺ (_∈ ys) xs) (ys≼ : Suffix≡ ys zs)
    → (proj₁ ∘ ∈⇒Suffix ∘ All⁺-last ∘ L.All.map (Suffix⇒⊆ ys≼)) ∀x∈
    ≡ (proj₁ ∘ ∈⇒Suffix ∘ All⁺-last) ∀x∈

-- ** Interleaving.
open import Data.List.Relation.Ternary.Interleaving using (_∷ˡ_; _∷ʳ_)

_∥_≡_ : 3Rel (List A) _
_∥_≡_ = Interleaving _≡_ _≡_

pattern keepˡ p = refl ∷ˡ p
pattern keepʳ p = refl ∷ʳ p

-- ** Finite sets.
Finite : Set a → Set a
Finite A = ∃[ n ] (A Fun.↔ Fin n)

finList : Finite A → List A
finList (n , record {f⁻¹ = Fin→A }) = map Fin→A (allFin n)

≡-findec : Finite A → Decidable² {A = A} _≡_
≡-findec (_ , record { f = toFin; f⁻¹ = fromFin; cong₂ = cong′; inverse = _ , invˡ }) x y
  with toFin x F.≟ toFin y
... | yes x≡y = yes (begin x                 ≡⟨ sym (invˡ x) ⟩
                           fromFin (toFin x) ≡⟨ cong′ x≡y ⟩
                           fromFin (toFin y) ≡⟨ invˡ y ⟩
                           y ∎)
                where open ≡-Reasoning
... | no  x≢y = no λ{ refl → x≢y refl }
