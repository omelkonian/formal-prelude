{-# OPTIONS --safe #-}
module Prelude.Lists.Suffix where

import Data.List.Relation.Binary.Pointwise as PW

open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.Bifunctor

private variable A : Type ℓ

-- ** Suffix relation, instantiated for propositional equality.
Suffix≡ : List A → List A → Type _
Suffix≡ = Suffix _≡_

suffix-refl : (xs : List A) → Suffix≡ xs xs
suffix-refl xs = here (PW.≡⇒Pointwise-≡ refl)

∈⇒Suffix : {x : A} {ys : List A}
  → x ∈ ys
  → ∃[ xs ] Suffix≡ (x ∷ xs) ys
∈⇒Suffix {ys = x ∷ xs}  (here refl) = xs , here (refl ∷ PW.refl refl)
∈⇒Suffix {ys = _ ∷ ys′} (there x∈) = map₂′ there (∈⇒Suffix x∈)
