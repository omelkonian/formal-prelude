module Prelude.Functor where

open import Prelude.Init

private variable ℓ : Level

Functor : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
Functor {ℓ = ℓ} = RawFunctor {ℓ = ℓ} {ℓ′ = ℓ}
open RawFunctor ⦃ ... ⦄ public

fmap = _<$>_

instance
  Functor-Maybe : Functor {ℓ} Maybe
  Functor-Maybe = M.Cat.functor

  Functor-List : Functor {ℓ} List
  Functor-List = L.Cat.functor

  Functor-List⁺ : Functor {ℓ} List⁺
  Functor-List⁺ = L.NE.Cat.functor

  Functor-Vec : ∀ {n} → Functor {ℓ} (flip Vec n)
  Functor-Vec = V.Cat.functor

  Functor-TC : Functor {ℓ} Meta.TC
  Functor-TC ._<$>_ = M._<$>_
    where import Reflection.TypeChecking.MonadSyntax as M
