module Prelude.Functor where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Set'

private
  variable
    ℓ : Level
    n : ℕ

Functor : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
Functor {ℓ = ℓ} = RawFunctor {ℓ = ℓ} {ℓ′ = ℓ}
open RawFunctor {{...}} public

fmap = _<$>_

instance
  Functor-Maybe : Functor {ℓ} Maybe
  Functor-Maybe = M.Cat.functor

  Functor-List : Functor {ℓ} List
  Functor-List = L.Cat.functor

  Functor-Vec : Functor {ℓ} (flip Vec n)
  Functor-Vec = V.Cat.functor

  Functor-TC : Functor {ℓ} Meta.TC
  Functor-TC ._<$>_ = M._<$>_
    where import Reflection.TypeChecking.MonadSyntax as M

  -- Functor-Set' : Functor {0ℓ} λ A {{_ : DecEq A}} → Set⟨ A ⟩
  -- Functor-Set' ._<$>_ f = (f <$>_) ∘ list
