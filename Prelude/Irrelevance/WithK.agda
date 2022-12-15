{-# OPTIONS --safe --with-K #-}
module Prelude.Irrelevance.WithK where

open import Prelude.Init; open SetAsType
open import Prelude.Irrelevance.Core

private variable A : Type ℓ

instance
  ·-≡ : ∀ {x y : A} → · (x ≡ y)
  ·-≡ .∀≡ refl refl = refl
