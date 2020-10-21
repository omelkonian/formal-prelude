------------------------------------------------------------------------
-- Maps with list witness, paired with a total function.
------------------------------------------------------------------------
module Prelude.Maps where

open import Prelude.Init
open L.Any using (index)
open import Prelude.DecEq
open import Prelude.Lists hiding (_⁉_)
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.Monoid
open import Prelude.Nary

record Map (K : Set) {{_ : DecEq K}} (V : Set) : Set where
  constructor ⟨_⟩∶-_
  field
    keys   : List K
    lookup : keys ↦ V
open Map public

module _ {K : Set} {{_ : DecEq K}} {V : Set} where

  _⁉_ : Map K V → K → Maybe V
  (⟨ ks ⟩∶- f) ⁉ k with k ∈? ks
  ... | yes k∈ = just (f k∈)
  ... | no  _  = nothing

  ∅ : Map K V
  ∅ = ⟨ [] ⟩∶- λ ()

  singleton : K → V → Map K V
  singleton k v = ⟨ [ k ] ⟩∶- λ{ (here _) → v; (there ()) }

  extendWith : (V → V → V) → (K × V) → Map K V → Map K V
  extendWith _⊚_ (k , v) (⟨ ks ⟩∶- f) with k ∈? ks
  ... | no  k∉ = ⟨ k ∷ ks ⟩∶- λ{ (here refl) → v; (there k∈) → f k∈ }
  ... | yes k∈ = ⟨ ks     ⟩∶- λ k∈′ → if index k∈ == index k∈′ then f k∈′ ⊚ v else f k∈′

  extend : (K × V) → Map K V → Map K V
  extend = extendWith (λ _ v → v)

  fromList : List (K × V) → Map K V
  fromList = foldr extend ∅

  toList : Map K V → List (K × V)
  toList (⟨ ks ⟩∶- f) = mapWith∈ ks λ {k} k∈ → k , f k∈

  unionWith : (V → V → V) → Map K V → Map K V → Map K V
  unionWith _⊚_ m m′ = foldr (extendWith _⊚_) m (toList m′)

  instance
    Functor-Map : Functor (Map K)
    Functor-Map ._<$>_ f (⟨ ks ⟩∶- g) = ⟨ ks ⟩∶- (f ∘ g)

    Semigroup-Map : Semigroup (Map K V)
    Semigroup-Map ._◇_ = unionWith (λ _ v → v)

    Monoid-Map : Monoid (Map K V)
    Monoid-Map .ε = ∅

{-
    DecEq-↦ : ∀ {xs : List K} → DecEq (xs ↦ V)
    DecEq-↦ {xs = []} ._≟_ f f′ = {!!}
    DecEq-↦ {xs = x ∷ xs} ._≟_ f f′ = {!!}

    DecEq-Map : DecEq (Map K V)
    DecEq-Map ._≟_ m m′
      with keys m ≟ keys m′
    ... | no ¬p    = no λ{ refl → ¬p refl }
    ... | yes refl
      with lookup m ≟ lookup m′
    ... | no ¬p    = no λ{ refl → ¬p refl }
    ... | yes refl = yes refl
-}

t : Map ℕ String
t = singleton 42 "nope" ◇ singleton 42 "yep"
