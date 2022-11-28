module Prelude.Maps.Examples where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.FromList

private
  module Implementation1 {K V : Type} ⦃ _ : DecEq K ⦄ where
    open import Prelude.Maps.Abstract.Interface
    import Prelude.Maps.AsPartialFunctions {K = K} {V = V} as Imp
    imp : FinMapᴵ K V 0ℓ
    imp = record {mapᴵ = record {Imp}; Imp}
    open FinMapᴵ imp public

  module Implementation2 {K V : Type} ⦃ _ : DecEq K ⦄ ⦃ _ : DecEq V ⦄ where
    open import Prelude.Maps.Abstract.Interface
    import Prelude.Maps.AsSets {K = K} {V = V} as Imp
    imp : Mapᴵ K V 0ℓ
    imp = record {Imp; ♯-comm = λ {x}{y} → Imp.♯-comm {x}{y}}
    open Mapᴵ imp public

  module Implementation3 where
    open import Prelude.Maps.AsSortedUniqueLists
    open import Prelude.ToList; open import Prelude.FromList
    open import Prelude.Ord; open import Prelude.Irrelevance

    _ = toList (Map⟨ ℕ ↦ ℕ ⟩ ∋ fromList
        ((0 , 00) ∷ (5 , 55) ∷ (2 , 22) ∷ (0 , 11) ∷ []))
      ≡ ((0 , 11) ∷ (2 , 22) ∷ (5 , 55) ∷ [])
      ∋ refl

    -- T0D0: cover abstract signature
    -- open import Prelude.Maps.Abstract.Interface
    -- import Prelude.Maps.AsSortedUniqueLists as Imp

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

    _ = Map ∋ m ∪ ∅
      where postulate m : Map⟨ K ↦ V ⟩

    _ = Map ∋ buildMap (const nothing) ∪ buildMap (λ k → just (f k))
      where postulate f : K → V

    _ = Map ∋ singleton (k , v) ∪ singleton (k , v)
      where postulate k : K; v : V

  module ConcreteExample where
    open import Prelude.Maps

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

    _ = (k↦ 10 ◇ k↦ 20) ≡ (k↦ 30)
      ∋ refl
      where instance _ = Semigroup-ℕ-+

    postulate v v′ v″ : ℕ

    _ = singleton (k , v) ≡ fromList [ k , v ]
      ∋ refl

    k↦v   = k↦  v; k↦v′  = k↦  v′; k↦v″  = k↦  v″
    k′↦v′ = k′↦ v′

    _ = (k↦v ∪ k′↦v′) ≡ fromList ((k , v) ∷ (k′ , v′) ∷ [])
      ∋ refl

    m₁ = Map
       ∋ singleton (k , v) ∪ singleton (k , v)
