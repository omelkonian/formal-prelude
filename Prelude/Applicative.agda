module Prelude.Applicative where

open import Prelude.Init

private
  variable
    ℓ : Level

Applicative : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
Applicative {ℓ = ℓ} = RawApplicative {f = ℓ}
open RawApplicative {{...}} public
  renaming (_⊛_ to _<*>_)

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
    where import Reflection.TypeChecking.MonadSyntax as M

  -- Applicative-∃Vec : Applicative {ℓ} (∃ ∘ Vec)
  -- Applicative-∃Vec = record { pure = λ x → 1 , pure x ; _⊛_ = λ{ (_ , v) (_ , v′) → _ , (V._⊛_ v v′) } }
