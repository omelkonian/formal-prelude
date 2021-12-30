------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of ternary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Relation.Ternary`.

{-# OPTIONS --without-K --safe #-}

module Relation.Ternary.Core where

open import Data.Product using (_×_)
open import Function.Base using (_on_)
open import Level using (Level; _⊔_; suc)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

-- Heterogeneous ternary relations

3REL : Set a → Set b → Set c → (ℓ : Level) → Set (a ⊔ b ⊔ c ⊔ suc ℓ)
3REL A B C ℓ = A → B → C → Set ℓ

-- Homogeneous ternary relations

3Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
3Rel A ℓ = 3REL A A A ℓ

------------------------------------------------------------------------
-- Relationships between relations
------------------------------------------------------------------------

infix 4 _⇒_ _⇔_ _=[_]⇒_

-- Implication/containment - could also be written _⊆_.
-- and corresponding notion of equivalence

_⇒_ : 3REL A B C ℓ₁ → 3REL A B C ℓ₂ → Set _
P ⇒ Q = ∀ {x y z} → P x y z → Q x y z

_⇔_ : 3REL A B C ℓ₁ → 3REL A B C ℓ₂ → Set _
P ⇔ Q = P ⇒ Q × Q ⇒ P

-- Generalised implication - if P ≡ Q it can be read as "f preserves P".

-- _on_ : (B → B → C) → (A → B) → (A → A → C)
-- _*_ on f = f -⟨ _*_ ⟩- f

_on³_ : (B → B → B → C) → (A → B) → (A → A → A → C)
(_~_~_ on³ f) x y z = f x ~ f y ~ f z

_=[_]⇒_ : 3Rel A ℓ₁ → (A → B) → 3Rel B ℓ₂ → Set _
P =[ f ]⇒ Q = P ⇒ (Q on³ f)

-- A synonym for _=[_]⇒_.

_Preserves_⟶_ : (A → B) → 3Rel A ℓ₁ → 3Rel B ℓ₂ → Set _
f Preserves P ⟶ Q = P =[ f ]⇒ Q

-- A ternary variant of _Preserves_⟶_.

_Preserves_⟶_⟶_ : (A → B → C) → 3Rel A ℓ₁ → 3Rel B ℓ₂ → 3Rel C ℓ₃ → Set _
_∙_ Preserves P ⟶ Q ⟶ R = ∀ {x y z u v w} → P x y z → Q u v w → R (x ∙ u) (y ∙ v) (z ∙ w)
