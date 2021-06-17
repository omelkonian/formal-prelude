module Prelude.Applicative where

open import Prelude.Init

Applicative : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
Applicative {ℓ = ℓ} = RawApplicative {f = ℓ}
open RawApplicative ⦃ ... ⦄ public
  using (pure)
  renaming ( _⊛_ to _<*>_; _<⊛_ to _<*_ ; _⊛>_ to _*>_)

instance
  Applicative-Maybe : Applicative {ℓ} Maybe
  Applicative-Maybe = M.Cat.applicative

  Applicative-List : Applicative {ℓ} List
  Applicative-List = L.Cat.applicative

  Applicative-List⁺ : Applicative {ℓ} List⁺
  Applicative-List⁺ = L.NE.Cat.applicative

  Applicative-Vec : ∀ {n} → Applicative {ℓ} (flip Vec n)
  Applicative-Vec = V.Cat.applicative

  Applicative-TC : Applicative {ℓ} Meta.TC
  Applicative-TC = record {pure = M.pure; _⊛_ = M._<*>_}
    where import Reflection.TypeChecking.Monad.Syntax as M

  -- Applicative-∃Vec : Applicative {ℓ} (∃ ∘ Vec)
  -- Applicative-∃Vec = record { pure = λ x → 1 , pure x ; _⊛_ = λ{ (_ , v) (_ , v′) → _ , (V._⊛_ v v′) } }

record Applicative₀ (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    overlap ⦃ ap ⦄ : Applicative F
    ε₀ : ∀ {A} → F A
open Applicative₀ ⦃ ... ⦄ hiding (ap) public

instance
  Applicative₀-Maybe : Applicative₀ {ℓ} Maybe
  Applicative₀-Maybe .ε₀ = nothing

  Applicative₀-List : Applicative₀ {ℓ} List
  Applicative₀-List .ε₀ = []

  Applicative₀-Vec : Applicative₀ {ℓ} (flip Vec 0)
  Applicative₀-Vec .ε₀ = []

record Alternative (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    overlap ⦃ ap₀ ⦄ : Applicative₀ F
    _<|>_ : ∀ {A} → F A → F A → F A
open Alternative ⦃ ... ⦄ hiding (ap₀) public

instance
  Alternative-Maybe : Alternative {ℓ} Maybe
  Alternative-Maybe ._<|>_ = M._<∣>_

  Alternative-List : Alternative {ℓ} List
  Alternative-List ._<|>_ = _++_
