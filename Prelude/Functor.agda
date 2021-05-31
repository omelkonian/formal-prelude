module Prelude.Functor where

open import Prelude.Init

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

  Functor-Abs : Functor Meta.Abs
  Functor-Abs ._<$>_ = A.map
    where import Reflection.Abstraction as A

  Functor-Arg : Functor {ℓ} Meta.Arg
  Functor-Arg ._<$>_ = A.map
    where import Reflection.Argument as A
