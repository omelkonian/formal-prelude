------------------------------------------------------------------------
-- Maps as functions from a Listable type to a Maybe type.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Listable
open import Prelude.Functor

module Prelude.Map'' {K V : Set} {{_ : DecEq K}} {{_ : Listable K}} where

Map : Set
Map = K → Maybe V
syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

dom : Map → List K
dom m = mapMaybe (λ k → const k <$> m k) witness

codom : Map → List V
codom m = mapMaybe m witness

set : Map → K → V → Map
set m k v k′ =
  if k == k′ then
    just v
  else
    m k′
syntax set m k v = m [ k ≔ v ]

-- update : Map → K → (V → V) → Map'
-- update m k f k′ with
--   m k′
-- ... | just v  = ?
-- ... | nothing = ?
  -- if k == k′ then

  -- else
  --   ∘ m

-- with m k
-- ... | just v  = ?
-- ... | nothing = just v

  -- ks , λ {k} → (if k == k′ then f else (λ x → x)) ∘ k↦
{-

update-const : ∀ {m k f} → dom m ≡ dom (update m k f)
update-const = refl

updateWith : Map' → K → V → (V → V) → Map'
updateWith m@(ks , k↦) k k-def f with k ∈′? ks
... | yes k∈ = ks           , f ∘ k↦
... | no  k∉ = k ∷ ks ∶- k∉ , λ{ (here refl) → f k-def; (there k∈′) → k↦ k∈′ }

-- we get extra utilities if we can get a default value when there is no entry for a particular key
module _ {{_ : Default V}} where
  update-with-def : Map' → K → (V → V) → Map'
  update-with-def m k f = updateWith m k def f


_≡ᵐ_ : Map' → Map' → Set
m ≡ᵐ m′ = (dom m ≡ dom m′) × (codom m ≡ codom m′)

postulate
  union-comm : ∀ {m m′} → union m m′ ≡ᵐ union m′ m
  ≡ᵐ-trans : ∀ {m m′ m″} → m ≡ᵐ m′ → m′ ≡ᵐ m″ → m ≡ᵐ m″
-- union-comm {m = xs , X} {m′ = ys , Y}
--   with _ , X∪Y ← union (xs , X) (ys , Y)
--   with _ , Y∪X ← union (ys , Y) (xs , X)
--   rewrite ∪-comm {xs = xs}{ys}
--     = refl , p
--     where
--       p : codom (_ , X∪Y) ≡ codom (_ , Y∪X)
--       p = ?

-- update-comm : ∀ {m k f k′ f′}
--   → [T0D0] f ∘ f' = f' ∘ f
--   → update (update m k f) k′ f′
--   ≡ update (update m k′ f′) k f
-- update-comm {m@(ks , k↦)}{k}{f}{k′}{f′}
--   with k ∈′? ks | k′ ∈′? ks
-- ... | yes k∈ | yes k∈′ = {!!}
-- ... | yes k∈ | no  k∉′ = {!!}
-- ... | no  k∉ | yes k∈′ = {!!}
-- ... | no  k∉ | no  k∉′ = {!!}


-- update m k f
-- m ∥ k ≔ f
-- m

-- update : ∀ {K V : Set} {{_ : DecEq K}} {ks : List K} {k : K}
--   → ks ↦ V
--   → (k ∈ ks) × (V → V)
--   → ks ↦ V
-- update {k = k} m (k∈ , f) {k′} k∈′
--   with v ← m k∈′
--   with k ≟ k′
-- ... | yes refl = f v
-- ... | no  ¬p   = v

-- updateˢ : S → Part × ℤ × (ℤ → ℤ) → S
-- updateˢ (ps , s) (p , pz , f)
--   with p ∈? ps
-- ... | yes p∈ = _ , update s (p∈ , f)
-- ... | no  p∉ = p ∷ ps , s′
--   where
--     s′ : (p ∷ ps) ↦ ℤ
--     s′ (here refl) = f pz
--     s′ (there p∈′) = s p∈′

-- update : ∀ {K V : Set} {xs : List K}
--   → ∃ (
--   → K
--   → (V → V)
--   → ∃ (_↦ V)
-- update {K}{V}{xs} (xs , f) x mod
--   with x ∈ xs
-- ... | yes x∈ = f x∈
-- ... | no  x∉ =
-}
