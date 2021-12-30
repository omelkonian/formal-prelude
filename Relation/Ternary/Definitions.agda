------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `3Relation.Ternary`.

{-# OPTIONS --without-K --safe #-}

module Relation.Ternary.Definitions where

open import Agda.Builtin.Equality using (_≡_)

open import Data.Maybe.Base using (Maybe)
open import Data.Product using (_×_)
open import Data.Sum.Base using (_⊎_)
open import Function.Base using (_on_; flip)
open import Level
open import Relation.Ternary.Core
open import Relation.Nullary using (Dec; ¬_)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

-- Reflexivity - defined without an underlying equality. It could
-- alternatively be defined as `_≈_ ⇒ _~_~_` for some equality `_≈_`.

-- Confusingly the convention in the library is to use the name "refl"
-- for proofs of Reflexive and `reflexive` for proofs of type `_≈_ ⇒ _~_~_`,
-- e.g. in the definition of `IsEquivalence` later in this file. This
-- convention is a legacy from the early days of the library.

Reflexive : 3Rel A ℓ → Set _
Reflexive _~_~_ = ∀ {x} → x ~ x ~ x

-- Decidability - it is possible to determine whether a given pair of
-- elements are related.

Decidable : 3REL A B C ℓ → Set _
Decidable _~_~_ = ∀ x y z → Dec (x ~ y ~ z)

-- Weak decidability - it is sometimes possible to determine if a given
-- pair of elements are related.

WeaklyDecidable : 3REL A B C ℓ → Set _
WeaklyDecidable _~_~_ = ∀ x y z → Maybe (x ~ y ~ z)

-- Irrelevancy - all proofs that a given pair of elements are related
-- are indistinguishable.

Irrelevant : 3REL A B C ℓ → Set _
Irrelevant _~_~_ = ∀ {x y z} (a b : x ~ y ~ z) → a ≡ b

-- Recomputability - we can rebuild a relevant proof given an
-- irrelevant one.

Recomputable : 3REL A B A ℓ → Set _
Recomputable _~_~_ = ∀ {x y z} → .(x ~ y ~ z) → x ~ y ~ z

-- Universal - all pairs of elements are related

Universal : 3REL A B C ℓ → Set _
Universal _~_~_ = ∀ x y z → x ~ y ~ z

-- Non-emptiness - at least one triple of elements are related.

record NonEmpty {A : Set a} {B : Set b} {C : Set c}
                (T : 3REL A B C ℓ) : Set (a ⊔ b ⊔ c ⊔ ℓ) where
  constructor nonEmpty
  field
    {x}   : A
    {y}   : B
    {z}   : C
    proof : T x y z
