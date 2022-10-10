module Prelude.Maps.Example where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.FromList

private
  module GeneralExample where
    open import Prelude.Maps

    _ = Map⟨ String ↦ ℕ ⟩
      ∋ singleton ("one" , 1) ∪ singleton ("two" , 2)

    _ = Map
      ∋ singleton ("one" , 1) ◇ singleton ("one" , 2)
      where instance _ = Semigroup-ℕ-+; _ = SemigroupLaws-ℕ-+
            instance _ = Monoid-ℕ-+;    _ = MonoidLaws-ℕ-+

  module AbstractExample where
    open import Prelude.Maps.Abstract

    K = ℕ; V = String
    open import Prelude.Maps.Abstract.TestImplementations {K = K} {V = V}

    _ = Map ∋ m ∪ ∅
      where postulate m : Map

    _ = Map ∋ buildMap (const nothing) ∪ buildMap (λ k → just (f k))
      where postulate f : K → V

    _ = Map ∋ singleton (k , v) ∪ singleton (k , v)
      where postulate k : K; v : V

  module ConcreteExample where
    open import Prelude.Maps.Concrete

    k = 0; k′ = 1
    k↦_  = (ℕ → Map⟨ ℕ ↦ ℕ ⟩) ∋ singleton ∘ (k ,_)
    k′↦_ = (ℕ → Map⟨ ℕ ↦ ℕ ⟩) ∋ singleton ∘ (k′ ,_)

    -- ** singleton

    _ = singleton (k , 10) ≡ fromList [ k , 10 ]
      ∋ refl

    -- ** _∪_

    _ = (k↦ 10 ∪ k′↦ 20) ≡ fromList ((k , 10) ∷ (k′ , 20) ∷ [])
      ∋ refl

    _ = (k↦ 10 ∪ k↦ 20) ≡ singleton (k , 20)
      ∋ refl

    -- ** insert/insertWith

    _ = insert (k′ , 20) (k↦ 10) ≡ (k↦ 10 ∪ k′↦ 20)
      ∋ refl
    _ = insert (k , 20) (k↦ 10) ≡ k↦ 20
      ∋ refl

    _ = insertWith _+_ (k′ , 20) (k↦ 10) ≡ (k↦ 10 ∪ k′↦ 20)
      ∋ refl
    _ = insertWith _+_ (k , 20) (k↦ 10) ≡ (k↦ 30)
      ∋ refl

    instance _ = Semigroup-ℕ-+
    _ = (k↦ 10 ◇ k↦ 20) ≡ (k↦ 30)
      ∋ refl
