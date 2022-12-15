{-# OPTIONS --safe #-}
module Prelude.Traversable where

open import Prelude.Init; open SetAsType
open import Prelude.Functor
open import Prelude.Foldable
open import Prelude.Applicative
open import Prelude.Monad

private variable A : Type ℓ; B : Type ℓ′; M : Type↑

record TraversableA (F : Type↑) ⦃ _ : Functor F ⦄ ⦃ _ : Foldable F ⦄ : Typeω where
  field
    sequenceA : ⦃ Applicative M ⦄ → F (M A) → M (F A)

  traverseA : ⦃ Applicative M ⦄ → (A → M B) → F A → M (F B)
  traverseA f = sequenceA ∘ fmap f

open TraversableA ⦃...⦄ public

record TraversableM (F : Type↑) ⦃ _ : Functor F ⦄ ⦃ _ : Foldable F ⦄ : Typeω where
  field
    sequenceM : ⦃ Monad M ⦄ → F (M A) → M (F A)

  traverseM : ⦃ Monad M ⦄ → (A → M B) → F A → M (F B)
  traverseM f = sequenceM ∘ fmap f

open TraversableM ⦃...⦄ public

instance
  TraversableA-Maybe : TraversableA  Maybe
  TraversableA-Maybe .sequenceA nothing  = pure nothing
  TraversableA-Maybe .sequenceA (just x) = ⦇ just x ⦈

  TraversableM-Maybe : TraversableM Maybe
  TraversableM-Maybe .sequenceM = sequenceA

  TraversableA-List : TraversableA List
  TraversableA-List .sequenceA = go where go = λ where
    []       → pure []
    (m ∷ ms) → ⦇ m ∷ go ms ⦈

  TraversableM-List : TraversableM List
  TraversableM-List .sequenceM = sequenceA

  TraversableA-List⁺ : TraversableA List⁺
  TraversableA-List⁺ .sequenceA (m ∷ ms) = ⦇ m ∷ sequenceA ms ⦈

  TraversableM-List⁺ : TraversableM List⁺
  TraversableM-List⁺ .sequenceM = sequenceA
