------------------------------------------------------------------------
-- Maps as (partial) functions to Maybe.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Listable
open import Prelude.Functor

module Prelude.PartialMaps {K V : Set} where

Map : Set
Map = K → Maybe V
syntax Map {K} {V} = Map⟨ K ↦ V ⟩

_∈ᵈ_ : K → Map → Set
k ∈ᵈ m = Is-just (m k)

_∉ᵈ_ : K → Map → Set
k ∉ᵈ m = Is-nothing (m k)

_[_↦_] : Map → K → V → Set
m [ k ↦ v ] = m k ≡ just v

_♯_ : Rel₀ Map
m ♯ m′ = ∀ k → (k ∈ᵈ m → k ∉ᵈ m′) × (k ∈ᵈ m′ → k ∉ᵈ m)

_∪_∶-_ : ∀ m m′ → m ♯ m′ → Map
(m ∪ m′ ∶- m♯m′) k
  with m k
... | nothing = m′ k
... | just v  = just v

_∪_≡_ : Map → Map → Map → Set
m ∪ m′ ≡ m″ = Σ[ p ∈ m ♯ m′ ] (∀ k → (m ∪ m′ ∶- p) k ≡ m″ k)

-- _[_↝⟨_⟩_] : Map → K → V → K → Map
-- m [ k₁ ↝⟨ v ⟩ k₂ ]
--   with m k₁ | m k₂
-- ... | just v₁  | just v₂ = λ k → if k == k₁ then v₁ -ℤ v else if k == k₂ then v₂ +ℤ v else m k
-- ... | _        | _       = m

-- (m [ k₁ ↝⟨ v ⟩ k₂ ]) k =
--  if m k == nothing ∨ m k′ == nothing then
--    m k″
--  else
--  if k″ == k then
--    (-ℤ v) <$> m k
--  else if k″ == k′ then
--    (+ℤ v) <$> m k′
--  else
--    m k″

-- set : Map → K → V → Map
-- set m k v k′ =
--   if k == k′ then
--     just v
--   else
--     m k′
-- syntax set m k v = m [ k ≔ v ]
