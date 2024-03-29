{-# OPTIONS --safe #-}
module Prelude.Pointed where

open import Prelude.Init; open SetAsType

record Pointed (F : Type↑) : Typeω where
  field point : ∀ {A : Type ℓ} → A → F A
open Pointed ⦃...⦄ public

instance
  P-Maybe : Pointed Maybe
  P-Maybe .point = just

  P-List : Pointed List
  P-List .point = [_]

  P-List⁺ : Pointed List⁺
  P-List⁺ .point = L.NE.[_]

  P-Vec : Pointed (flip Vec 1)
  P-Vec .point = V.[_]

  P-TC : Pointed Meta.TC
  P-TC .point = M.pure
    where import Reflection.TypeChecking.Monad.Syntax as M
