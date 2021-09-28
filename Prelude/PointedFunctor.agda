module Prelude.PointedFunctor where

open import Prelude.Init
open import Prelude.Functor
open import Prelude.Applicative

record PointedFunctor (F : Set↑) : Setω where
  field
    overlap ⦃ super ⦄ : Functor F
    point : ∀ {A : Set ℓ} → A → F A

open PointedFunctor ⦃...⦄ public

instance
  -- [ISSUE] leads to unresolved metavariables
  -- Applicative⇒PFunctor : ∀ {F : Set ℓ → Set ℓ} ⦃ _ : Functor F ⦄ ⦃ _ : Applicative F ⦄ → PointedFunctor F
  -- Applicative⇒PFunctor .point = pure

  PFunctor-Maybe : PointedFunctor Maybe
  PFunctor-Maybe .point = just

  PFunctor-List : PointedFunctor List
  PFunctor-List .point = [_]

  PFunctor-List⁺ : PointedFunctor List⁺
  PFunctor-List⁺ .point = L.NE.[_]

  PFunctor-Vec : PointedFunctor (flip Vec 1)
  PFunctor-Vec .point = V.[_]

  PFunctor-TC : PointedFunctor Meta.TC
  PFunctor-TC .point = M.pure
    where import Reflection.TypeChecking.Monad.Syntax as M
