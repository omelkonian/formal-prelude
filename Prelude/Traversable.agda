module Prelude.Traversable where

open import Prelude.Init
open import Prelude.Functor
open import Prelude.Foldable
open import Prelude.Applicative
open import Prelude.Monad

record TraversableA (F : Set ℓ → Set ℓ) ⦃ _ : Functor F ⦄ ⦃ _ : Foldable F ⦄ : Set (lsuc ℓ) where
  field
    sequenceA : ∀ {A} {M : Set ℓ → Set ℓ} ⦃ _ : Applicative M ⦄ → F (M A) → M (F A)

  traverseA : ∀ {A B} {M : Set ℓ → Set ℓ} ⦃ _ : Applicative M ⦄ → (A → M B) → F A → M (F B)
  traverseA f = sequenceA ∘ fmap f

open TraversableA ⦃ ... ⦄ public

record TraversableM (F : Set ℓ → Set ℓ) ⦃ _ : Functor F ⦄ ⦃ _ : Foldable F ⦄ : Set (lsuc ℓ) where
  field
    sequenceM : ∀ {A} {M : Set ℓ → Set ℓ} ⦃ _ : Monad M ⦄ → F (M A) → M (F A)

  traverseM : ∀ {A B} {M : Set ℓ → Set ℓ} ⦃ _ : Monad M ⦄ → (A → M B) → F A → M (F B)
  traverseM f = sequenceM ∘ fmap f

open TraversableM ⦃ ... ⦄ public

instance
  TraversableA-Maybe : TraversableA {ℓ} Maybe
  TraversableA-Maybe .sequenceA nothing  = pure nothing
  TraversableA-Maybe .sequenceA (just x) = ⦇ just x ⦈

  TraversableM-Maybe : TraversableM {ℓ} Maybe
  TraversableM-Maybe .sequenceM nothing  = return nothing
  TraversableM-Maybe .sequenceM (just x) = x >>= return ∘ just

  TraversableA-List : TraversableA {ℓ} List
  TraversableA-List .sequenceA []       = pure []
  TraversableA-List .sequenceA (m ∷ ms) = ⦇ m ∷ sequenceA ms ⦈

  TraversableM-List : TraversableM {ℓ} List
  TraversableM-List .sequenceM []       = return []
  TraversableM-List .sequenceM (m ∷ ms) = do x ← m; xs ← sequenceM ms; return (x ∷ xs)
