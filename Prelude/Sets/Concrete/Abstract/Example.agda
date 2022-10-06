module Prelude.Sets.Concrete.Abstract.Example where

open import Prelude.Init
open import Prelude.DecEq

module ConcreteExample where
  open import Prelude.Sets.Concrete

  _ : 1 ∈ˢ (singleton 0 ∪ singleton 1 ∪ singleton 2)
  _ = there (here refl)

module AbstractExample where
  open import Prelude.Sets.Concrete.Abstract

  _ : 1 ∈ˢ (singleton 0 ∪ singleton 1 ∪ singleton 2)
  -- _ = there (here refl) -- DOES NOT COMPUTE, AS EXPECTED!
  _ = ∈-∪⁺ʳ _ _ _ (∈-∪⁺ˡ _ _ _ (singleton∈ˢ .proj₂ refl))
