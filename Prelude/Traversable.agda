module Prelude.Traversable where

open import Prelude.Init
open import Prelude.Functor
open import Prelude.Foldable
open import Prelude.Applicative
open import Prelude.Monad

private variable A : Set ℓ; B : Set ℓ′; M : Set↑

record TraversableA (F : Set↑) ⦃ _ : Functor F ⦄ ⦃ _ : Foldable F ⦄ : Setω where
  field
    sequenceA : ⦃ Applicative M ⦄ → F (M A) → M (F A)

  traverseA : ⦃ Applicative M ⦄ → (A → M B) → F A → M (F B)
  traverseA f = sequenceA ∘ fmap f

open TraversableA ⦃ ... ⦄ public

record TraversableM (F : Set↑) ⦃ _ : Functor F ⦄ ⦃ _ : Foldable F ⦄ : Setω where
  field
    sequenceM : ⦃ Monad M ⦄ → F (M A) → M (F A)

  traverseM : ⦃ Monad M ⦄ → (A → M B) → F A → M (F B)
  traverseM f = sequenceM ∘ fmap f

open TraversableM ⦃ ... ⦄ public

instance
  TraversableA-Maybe : TraversableA  Maybe
  TraversableA-Maybe .sequenceA nothing  = pure nothing
  TraversableA-Maybe .sequenceA (just x) = ⦇ just x ⦈

  TraversableM-Maybe : TraversableM Maybe
  TraversableM-Maybe .sequenceM nothing  = return nothing
  TraversableM-Maybe .sequenceM (just x) = x >>= return ∘ just

  TraversableA-List : TraversableA List
  TraversableA-List .sequenceA []       = pure []
  TraversableA-List .sequenceA (m ∷ ms) = ⦇ m ∷ sequenceA ms ⦈

  TraversableM-List : TraversableM List
  TraversableM-List .sequenceM []       = return []
  TraversableM-List .sequenceM (m ∷ ms) = do x ← m; xs ← sequenceM ms; return (x ∷ xs)

  TraversableA-List⁺ : TraversableA List⁺
  TraversableA-List⁺ .sequenceA (m ∷ ms) = ⦇ m ∷ sequenceA ms ⦈

  TraversableM-List⁺ : TraversableM List⁺
  TraversableM-List⁺ .sequenceM (m ∷ ms) = do x ← m; xs ← sequenceM ms; return (x ∷ xs)
